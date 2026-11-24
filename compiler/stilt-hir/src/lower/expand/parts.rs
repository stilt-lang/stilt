//! A procedural macro's use split into parts, each given to its parameter (macros.parts).
//!
//! The group is split at its commas outside nested groups: an empty group has no part, one
//! trailing comma is ignored, and an empty part is E0227 at the comma that ends it. A trailing
//! block's contents go to the last parameter, without the separators that newlines insert at
//! their top level, and the parts to the others in order. A `meta.Tokens` last parameter takes
//! every part from its own on, with the commas between them.

use stilt_diag::{Diagnostic, Edit, Fix, codes};
use stilt_syntax::SyntaxKind::{
    self, COMMA, L_BRACK, L_CURLY, L_PAREN, R_BRACK, R_CURLY, R_PAREN, STRING, STRING_HEAD,
    STRING_TAIL,
};
use stilt_syntax::forms::{Form, Piece, parse_form};
use stilt_syntax::{TextRange, TextSize};

use super::super::Resolver;
use super::procedural::{Brackets, relative};
use crate::hir::{CodeForm, Input};
use crate::macros::substitute::Tok;
use crate::procs::Given;

/// A token of a use, and whether it is a separator that a newline inserted.
#[derive(Clone, Debug)]
pub(super) struct UseTok {
    pub(super) tok: Tok,
    pub(super) inserted: bool,
}

/// A part: the indices of its tokens, and the index of the comma or bracket after it.
struct Part {
    tokens: Vec<usize>,
    after: usize,
}

/// Why a use gives its macro nothing: where, what is wrong there, and the fix, where one
/// writes the use as the macro takes it.
pub(super) type Unfit = (TextRange, String, Option<Fix>);

fn unfit(at: TextRange, why: impl Into<String>) -> Unfit {
    (at, why.into(), None)
}

fn opens(kind: SyntaxKind) -> bool {
    matches!(kind, L_PAREN | L_BRACK | L_CURLY | STRING_HEAD)
}

fn closes(kind: SyntaxKind) -> bool {
    matches!(kind, R_PAREN | R_BRACK | R_CURLY | STRING_TAIL)
}

/// The indices of the tokens strictly between an opening bracket at `open` and its closing one
/// at `close`, at their top level and below, without the separators newlines inserted at
/// their top level when `written` is set.
fn inside(tokens: &[UseTok], open: usize, close: usize, written: bool) -> Vec<usize> {
    let mut depth = 0usize;
    let mut out = Vec::new();
    for (i, t) in tokens.iter().enumerate().take(close).skip(open + 1) {
        if closes(t.tok.kind) {
            depth = depth.saturating_sub(1);
        }
        if !(written && depth == 0 && t.inserted) {
            out.push(i);
        }
        if opens(t.tok.kind) {
            depth += 1;
        }
    }
    out
}

/// The parts of a group's tokens, split at its commas outside nested groups.
fn split(tokens: &[UseTok], indices: &[usize], close: usize) -> Result<Vec<Part>, Unfit> {
    let mut parts = Vec::new();
    let mut current = Vec::new();
    let mut depth = 0usize;
    for &i in indices {
        let kind = tokens[i].tok.kind;
        if closes(kind) {
            depth = depth.saturating_sub(1);
        }
        if depth == 0 && kind == COMMA {
            if current.is_empty() {
                let fix = Fix::new("delete the comma", vec![Edit::delete(tokens[i].tok.at)]);
                let why = "this part is empty";
                return Err((tokens[i].tok.at, why.to_owned(), Some(fix)));
            }
            parts.push(Part {
                tokens: std::mem::take(&mut current),
                after: i,
            });
        } else {
            current.push(i);
        }
        if opens(kind) {
            depth += 1;
        }
    }
    if !current.is_empty() {
        parts.push(Part {
            tokens: current,
            after: close,
        });
    }
    Ok(parts)
}

fn form_of(form: CodeForm) -> Form {
    match form {
        CodeForm::Expr | CodeForm::Field => Form::Expr,
        CodeForm::Pattern => Form::Pattern,
        CodeForm::Type => Form::Type,
    }
}

/// What each parameter takes from a use whose tokens are `tokens`, with the indices of its
/// group's brackets and of its trailing block's, or why the use gives the macro nothing.
pub(super) fn given(
    (inputs, start): (&[Input], TextSize),
    tokens: &[UseTok],
    (group, block): Brackets,
) -> Result<Vec<Given>, Unfit> {
    let indices = inside(tokens, group.0, group.1, false);
    let parts = split(tokens, &indices, group.1)?;
    let Some((open, close)) = block else {
        return matched((inputs, start), tokens, &parts, (&indices, group.1));
    };
    let Some((last, others)) = inputs.split_last() else {
        return Err(unfit(tokens[open].tok.at, "this block is one too many"));
    };
    let mut given = matched((others, start), tokens, &parts, (&indices, group.1))?;
    let body = Part {
        tokens: inside(tokens, open, close, true),
        after: close,
    };
    given.push(one((*last, start), tokens, &body)?);
    Ok(given)
}

/// The parts given in order to the parameters, a `meta.Tokens` last one taking every part from
/// its own on.
fn matched(
    (inputs, start): (&[Input], TextSize),
    tokens: &[UseTok],
    parts: &[Part],
    (all, close): (&[usize], usize),
) -> Result<Vec<Given>, Unfit> {
    let mut given = Vec::new();
    for (k, input) in inputs.iter().enumerate() {
        let last = k + 1 == inputs.len();
        match (input, parts.get(k)) {
            (Input::Tokens, part) if last => {
                let rest: Vec<u32> = match part {
                    Some(p) => {
                        let from = all.iter().position(|&i| i == p.tokens[0]).unwrap_or(0);
                        let mut rest = all[from..].to_vec();
                        if rest.last().is_some_and(|&i| tokens[i].tok.kind == COMMA) {
                            rest.pop();
                        }
                        rest.into_iter().map(index).collect()
                    }
                    None => Vec::new(),
                };
                let close = relative(start, tokens[close].tok.at);
                given.push(Given::Tokens(rest, close));
                return Ok(given);
            }
            (_, None) => {
                return Err(unfit(tokens[close].tok.at, "a part is missing here"));
            }
            (input, Some(part)) => given.push(one((*input, start), tokens, part)?),
        }
    }
    match parts.get(inputs.len()) {
        Some(extra) => Err(extra_parts(tokens, parts, inputs.len(), extra)),
        None => Ok(given),
    }
}

/// What one part gives its parameter: code of its form, whole, a string literal without
/// interpolation, or its tokens.
fn one((input, start): (Input, TextSize), tokens: &[UseTok], part: &Part) -> Result<Given, Unfit> {
    let at = |i: usize| tokens[i].tok.at;
    let first = part.tokens.first().map_or(at(part.after), |&i| at(i));
    match input {
        Input::Code(form) => {
            let pieces: Vec<Piece<'_>> = part
                .tokens
                .iter()
                .map(|&i| Piece {
                    kind: tokens[i].tok.kind,
                    text: &tokens[i].tok.text,
                })
                .collect();
            let parsed = parse_form(&pieces, form_of(form));
            if parsed.is_whole(pieces.len()) {
                return Ok(Given::Code(
                    form,
                    part.tokens.iter().map(|&i| index(i)).collect(),
                ));
            }
            let stop = parsed.error.unwrap_or(parsed.taken);
            Err(match part.tokens.get(stop) {
                Some(&i) => unfit(at(i), format!("this part isn't {} here", form.describe())),
                None => unfit(at(part.after), "this part ends before its form does"),
            })
        }
        Input::Text | Input::File => match part.tokens.as_slice() {
            [i] if tokens[*i].tok.kind == STRING => Ok(if input == Input::File {
                Given::File(index(*i), String::new())
            } else {
                Given::Text(index(*i))
            }),
            _ => Err(unfit(
                first,
                "this part isn't a string literal without interpolation, which its parameter \
                 takes",
            )),
        },
        Input::Tokens => Ok(Given::Tokens(
            part.tokens.iter().map(|&i| index(i)).collect(),
            relative(start, at(part.after)),
        )),
    }
}

/// E0227 at the first part past the macro's last parameter, `extra`, whose fix deletes it and
/// the parts after it, with the comma before them.
fn extra_parts(tokens: &[UseTok], parts: &[Part], taken: usize, extra: &Part) -> Unfit {
    let at = |i: usize| tokens[i].tok.at;
    let from = match taken.checked_sub(1).and_then(|k| parts.get(k)) {
        Some(before) => at(before.after).start(),
        None => at(extra.tokens[0]).start(),
    };
    let last = parts
        .last()
        .and_then(|p| p.tokens.last())
        .map_or(at(extra.tokens[0]), |&i| at(i));
    // Without a part before it, a trailing comma goes too, which would end an empty part.
    let to = match parts.last() {
        Some(p) if taken == 0 && tokens.get(p.after).is_some_and(|t| t.tok.kind == COMMA) => {
            at(p.after).end()
        }
        _ => last.end(),
    };
    let title = if parts.len() - taken == 1 {
        "delete the extra part"
    } else {
        "delete the extra parts"
    };
    let fix = Fix::new(title, vec![Edit::delete(TextRange::new(from, to))]);
    let why = "this part is one too many";
    (at(extra.tokens[0]), why.to_owned(), Some(fix))
}

impl Resolver<'_> {
    /// Reads the files that `File` parts name (macros.named-files), or reports E0229 at the literal
    /// of each that can't be read.
    pub(super) fn read_files(&mut self, tokens: &[UseTok], given: &mut [Given]) -> bool {
        let mut read = true;
        for g in given.iter_mut() {
            let Given::File(i, text) = g else { continue };
            let literal = &tokens[*i as usize].tok;
            let path = stilt_syntax::text::literal_value(&literal.text);
            match crate::procs::read_file(self.db, self.program, self.module.file, &path) {
                Ok(contents) => *text = contents,
                Err(unread) => {
                    let d = Diagnostic::new(codes::E0229, literal.at, unread.why);
                    let fix = unread.meant.map(|meant| {
                        let text = format!("\"{}\"", escaped(&meant));
                        Fix::new(
                            format!("write `{meant}`"),
                            vec![Edit::replace(literal.at, text)],
                        )
                    });
                    self.diagnostics
                        .push(fix.into_iter().fold(d, Diagnostic::with_fix));
                    read = false;
                }
            }
        }
        read
    }
}

/// A path written in a string literal: `\\`, `"` and `{` escaped (lexical.escapes).
fn escaped(path: &str) -> String {
    let mut out = String::with_capacity(path.len());
    for c in path.chars() {
        if matches!(c, '\\' | '"' | '{') {
            out.push('\\');
        }
        out.push(c);
    }
    out
}

fn index(i: usize) -> u32 {
    u32::try_from(i).unwrap_or(u32::MAX)
}
