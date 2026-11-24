//! The formatter of Stilt, which writes a file in its one canonical format (syntax.format and
//! syntax.no-options): two spaces per level of indentation and no aligned columns, a brace on the
//! line of its construct, a block of one statement on one line when the line fits in 100 columns
//! and otherwise one statement per line, an `if` with an `else` on one line when it fits and
//! otherwise every branch on lines of its own, `match` and `catch` arms one per line, a record or
//! variant type on one line when it fits and otherwise one field or variant per line, each field
//! followed by a comma, no `;` or comma between arms, and record fields punned. It has no options.
//!
//! The format is a function of the syntax tree and the comments. Where the source puts its line
//! breaks decides nothing, so two sources with one tree format alike. Every construct goes on
//! one line when the whole line fits in 100 columns: the line up to it, the construct, and what
//! follows it up to the next place where a line may break. Otherwise it breaks, by these rules:
//!
//! - **Lists.** An argument list, a parameter list, a payload, a list, a tuple, a record literal
//!   and a pattern in brackets have one element per line, each followed by a comma, the last
//!   too, and the closing bracket on a line of its own. A tuple of one element keeps its comma
//!   when the list stays on one line, and the comma after a `..` that ends a pattern is never
//!   written. A list of one string doesn't break, since no break would shorten it. The lists
//!   inside an element are laid out again at its level.
//! - **Lists of literals.** A list literal whose elements are all numbers, possibly negated,
//!   strings or booleans, and which holds no comment, fills each line with as many elements as
//!   fit, each followed by a comma, instead.
//! - **Signatures.** A `without` clause goes on the line after its signature, a level in, with
//!   the body's `{`, when the signature with it doesn't fit on one line. A parameter list goes
//!   on one line only when the return type, the row and the `where` clause after it fit on that
//!   line too, so it breaks before they do. They then break by themselves on the line of its
//!   `)`. A function type's parameter list does the same.
//! - **Operators.** A binary expression breaks after each of its operators, and one of the same
//!   operator, as in `a + b + c`, is one group. An `else` fallback breaks before its `else`,
//!   unless it is a block. `>` and `>>` never end a line (lexical.continuing-expression). Lines that continue
//!   are a level in.
//! - **Chains.** A chain of two or more calls breaks before each `.` after its start, which is
//!   its first expression and the fields before its first call, as in `orders.items` in
//!   `orders.items.iter().map(f)`. Each call is a level in. A chain that doesn't fit keeps its
//!   line up to the arguments of its last call when that fits, and those break by themselves.
//! - **Closures.** A call whose last argument is a closure with a block keeps its line up to the
//!   block's brace when that fits, and the block's statements go one per line: `items.each(|i| {`.
//! - **Patterns.** Alternatives break before each `|`, a level in. A `try` breaks before a `catch`
//!   of one arm whose body isn't a block, and a `without` clause after a comma.
//! - **Fallbacks.** A block after `else`, a block-form `catch` and the block of a one-arm
//!   `catch` open on the line where the expression before them ends, and what they hold goes
//!   one level deeper than that line.
//! - **Branches.** An `if` with an `else` is one group, `else if` included: on one line when it
//!   fits, and otherwise the braces of every branch break, as in `} else {`.
//! - **Heads.** The lines that continue the condition of an `if` or a `while`, the iterable of a
//!   `for` or the scrutinee of a `match` are two levels in, so that the body, which is one level
//!   in, isn't mistaken for a part of the head. The body of a head that continues is one level
//!   in from the statement.
//! - **Everything else** stays on its line: the `->` of a return type and the row after it, the
//!   keys of a closure, a path, a type with its arguments, the `else` after a branch's `}`, and
//!   an interpolated string, which can't hold a raw newline (lexical.string-literals).
//!
//! The rest is decided by the tokens around the gaps:
//!
//! - **Comments** stay on their lines: a comment that ends a line stays after the token before
//!   it, and a comment alone on its line stays alone, at the level of the code after it. A
//!   construct that holds a comment never goes on one line, and a comment that ends a line
//!   doesn't count toward its 100 columns.
//! - **Blank lines** between two lines are kept, at most one, except right after an opening
//!   bracket or right before a closing one, and at the start and the end of the file.
//! - **Imports, items and arms** keep their order.
//! - **The module header** puts each `without` clause on a line of its own, at the level of
//!   the items (program.module-header).
//! - **Impls and traits** aren't blocks: their members go one per line.
//!
//! Three cases take more than the tree:
//!
//! - A statement that starts with `.` or `|`, which only a `;` can separate from the statement
//!   before it (lexical.terminator-insertion), goes in parentheses, which leave no trace in its tree.
//! - A `-` that the source separates from the number after it is a negation, not a part of the
//!   literal (numbers.negative-literals), so it keeps its space, which the tree doesn't show.
//! - An interpolation that holds a block, a `match` or a block-form `catch` is written as it is.
//!   Doc comments and other comments are written as they are, `/// ex:` examples included.
//!
//! Macros take only their tokens, since no macro is resolved when a file is formatted
//! (macros.formatting):
//!
//! - **Declarations.** A `syntax` declaration's arms go one per line, as a `match`'s do. Its
//!   patterns and templates aren't expressions, so each token is spaced by the token before it,
//!   as code spaces the same tokens: no space after a `$`, an opening bracket, a prefix `-` or
//!   `!`, a `.`, a `..` or a use's `!`, and none before a closing bracket, a `,`, a `:`, a `;`,
//!   a `.`, a `?` or a repetition's `*` or `+`. A `(` or a `[` goes against the operand before
//!   it, a `<` after an uppercase name opens type arguments, a `|` where no operand ends opens a
//!   closure's parameters, and one space goes everywhere else, as around `=>`: `$x: expr`,
//!   `$($x: expr),*`, `if !($cond) $body`. Two tokens that would read as another, as `-` and
//!   `>` would as `->`, keep a space between them, and so do a `-` and the number it is apart
//!   from (numbers.negative-literals).
//! - **Blocks in declarations.** A `{ … }` group that holds a separator, or holds such a group,
//!   is laid out as a block: a line for each run of its tokens between separators, a level in,
//!   and its `}` on a line of its own. Any other group stays on one line, however long, and a
//!   separator in it is a `;`. Where a line break wouldn't separate, after a token that ends no
//!   statement or before one that continues the line (lexical.terminator-insertion), a `;` ends the line,
//!   and so it ends an arm whose template ends with a repetition's `*`.
//! - **Uses.** A use's groups are written as they are, spaces and line breaks included. Each
//!   line inside one keeps its indentation relative to the line where the group opens, none
//!   when it has less, from the indentation of the line it is written on, a tab counting two
//!   columns, and the spaces that end a line go. A trailing block is a space after the group
//!   before it, and a construct that holds a group on several lines never goes on one line,
//!   as one that holds a comment doesn't.
//!
//! A file with a syntax error isn't formatted. Neither is a file that the formatter would give
//! another tree, or whose comments it would change, which would be a bug of the formatter's:
//! [`format`] checks both before it returns.
//!
//! Its place among the crates (`compiler/README.md`): it depends on `stilt-syntax` alone, and on
//! no phase after parsing.
#![warn(missing_docs)]
// Every module reads syntax kinds, which are the vocabulary of the grammar, so they are named
// unqualified, as in `stilt-syntax`.
#![allow(clippy::enum_glob_use)]

mod check;
mod render;
mod space;
mod stream;
mod trivia;
mod walk;

use stilt_syntax::Diagnostic;

use crate::stream::Builder;

/// Why a file wasn't formatted.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Error {
    /// The file has a syntax error, its first (errors.syntax-errors).
    Syntax(Diagnostic),
    /// The formatted text would parse to another tree, or hold other comments.
    Changed,
}

/// The text of a source file in the canonical format, which ends with a newline, unless the
/// file holds nothing but whitespace.
///
/// # Errors
///
/// [`Error::Syntax`] when the file has a syntax error, which includes text that isn't UTF-8
/// (lexical.source-text), and [`Error::Changed`] when the formatter would change what the file
/// means.
pub fn format(source: &[u8]) -> Result<String, Error> {
    format_wide(source, 0)
}

/// [`format`] with lines that may take `extra` columns more than 100, for a text that is to be
/// indented by `extra` columns afterwards, as the canonical text of a member is
/// (edits.canonical-text): the member is formatted at the level of an impl's members and its lines
/// are then shifted left, so that it fits as it would at column 0.
///
/// # Errors
///
/// As [`format`].
pub fn format_wide(source: &[u8], extra: usize) -> Result<String, Error> {
    let parse = stilt_syntax::parse_bytes(source);
    if let Some(error) = parse.error() {
        return Err(Error::Syntax(error.clone()));
    }
    let root = parse.syntax();
    let mut builder = Builder::new(trivia::collect(&root));
    walk::file(&root, &mut builder);
    let stream = builder.finish(u32::from(root.text_range().end()));
    let formatted = render::render(&stream, extra);
    // A text the formatter gives back unchanged keeps its tree and its comments, so only a
    // changed text is parsed again to be checked.
    if formatted.as_bytes() == source || check::same(&parse, &formatted) {
        Ok(formatted)
    } else {
        Err(Error::Changed)
    }
}

#[cfg(test)]
mod tests;
