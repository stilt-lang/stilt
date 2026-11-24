//! The grammar of core Stilt, as `reference/03-syntax.md` states it. Its submodules follow the
//! sections of that document.
//!
//! Each function decides what to read from the token under the cursor, and at most two tokens
//! past it, so that a syntax error is found at the first token that no program can continue
//! from, as the reference interpreter's LR(1) grammar finds it. Ambiguities are settled as the
//! grammar's "Settling ambiguities" section says: by binding powers that transcribe the Reference's
//! precedence table, and by each operand of level 14 reading as far to the right as it can.

mod control;
mod decls;
mod effects;
mod exprs;
mod lists;
mod macros;
mod module;
mod paths;
mod patterns;
mod quotes;
mod recovery;
mod stmts;
mod types;

pub(crate) use stmts::is_assign_op;

use self::exprs::{Mode, expr};
use self::module::{contents, file, is_item_start, items};
use self::stmts::stmt;
use crate::SyntaxKind::*;
use crate::parser::{ParseError, Parser};
use crate::sections::Part;
use crate::stream::Sig;

/// Where the parser starts.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum Entry {
    /// A source file.
    File,
    /// The expression of a doc example (program.doc-examples).
    Example,
    /// The text of a comment, read as statements or items to find commented-out code
    /// (lexical.commented-out-code).
    Code,
    /// A source file with a syntax error, read an item at a time (program.syntax-errors-at-run),
    /// whose tokens a lexical error ends when this holds.
    Parts(bool),
    /// An input of the REPL (repl.inputs).
    Input,
}

/// The parts of a file's tokens before `end`, cut before each token that begins an item and
/// follows a separator outside every bracket (errors.parts).
pub(crate) fn parts(tokens: &[Sig], end: usize) -> Vec<(usize, usize)> {
    recovery::parts(tokens, (0, end), 0, recovery::begins_item)
}

/// Parses a part alone, as a file, up to the parser's limit, and gives the error at which it
/// breaks, if it does.
pub(crate) fn part_error(p: &mut Parser<'_>) -> Option<ParseError> {
    let at = p.checkpoint();
    contents(p);
    p.first_error_since(at)
}

/// A file with a syntax error, whose stretches [`crate::sections`] read: each of its parts
/// alone, and again as the rule keeps it if it breaks.
pub(crate) fn parse_sections(p: &mut Parser<'_>, parts: &[Part]) {
    recovery::file_in_sections(p, parts);
}

pub(crate) fn parse(p: &mut Parser<'_>, entry: Entry) {
    match entry {
        Entry::File => file(p),
        Entry::Example => example(p),
        Entry::Code => code(p),
        Entry::Parts(lexical) => recovery::file_in_parts(p, lexical),
        Entry::Input => input(p),
    }
}

/// A form of a macro's expansion (macros.expansion): an expression, a pattern, a type or a
/// block, read from the token under the cursor for as long as it goes on.
pub(crate) fn form(p: &mut Parser<'_>, form: crate::forms::Form) {
    use crate::forms::Form;
    match form {
        Form::Expr => {
            expr(p, Mode::Full);
        }
        Form::Pattern => patterns::pattern(p),
        Form::Type => {
            types::ty(p);
        }
        Form::Block => stmts::block_expected(p),
    }
}

// Inputs of the REPL (repl.inputs): one statement, held in a block without braces.

fn input(p: &mut Parser<'_>) {
    let m = p.start();
    stmt(p);
    while p.at(SEP) {
        p.bump(SEP);
    }
    if !p.at(EOF) {
        p.error();
        p.skip_until(&[]);
    }
    m.complete(p, BLOCK);
}

// Doc examples (program.doc-examples)

fn example(p: &mut Parser<'_>) {
    let m = p.start();
    expr(p, Mode::Full);
    if !p.at(EOF) {
        p.error();
        p.skip_until(&[]);
    }
    m.complete(p, EXAMPLE);
}

// Commented-out code (lexical.commented-out-code): statements or items.

fn code(p: &mut Parser<'_>) {
    let m = p.start();
    if is_item_start(p.current()) {
        items(p);
    } else {
        stmt(p);
        while !p.at(EOF) {
            if !p.expect(SEP) {
                break;
            }
            stmt(p);
        }
    }
    m.complete(p, SOURCE_FILE);
}
