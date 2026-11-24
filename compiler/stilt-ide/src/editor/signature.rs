//! Signature help: the header of the function that the call around a position calls, as code
//! calls it, with the parameter being written. The call is found among the file's tokens, so
//! that a call not yet closed has one, and its function by what type checking resolved, or
//! else by its name: the module's, the prelude's or an imported module's function, or the
//! method of the type that its receiver's binding writes.

use stilt_db::{Database, Program, SourceFile};
use stilt_lsp::Signature;
use stilt_syntax::SyntaxKind::*;
use stilt_syntax::{SyntaxNode, SyntaxToken, TextSize};
use stilt_types::position::{Named, named_at};

use super::scope::written_type;
use crate::show::lookup::Parts;
use crate::show::position::{qualifier, resolve_written};

/// The signature of the function that the call around `offset` of `file` calls.
pub fn signature(
    db: &Database,
    program: Program,
    file: SourceFile,
    offset: u32,
) -> Option<Signature> {
    let root = stilt_db::parse(db, file).syntax();
    let (callee, mut active) = open_call(&root, TextSize::from(offset))?;
    let mut parts = Parts::new(db, program);
    let path = callee_path(db, program, file, &callee, &mut parts)?;
    let (of, i) = parts.declaration(&path)?;
    let header = of.header(i);
    let label = match qualifier(&of.parts[i].place) {
        Some(q) => format!("{q}.{header}"),
        None => header,
    };
    let params = params(&label);
    let after_dot = callee.prev_token().is_some_and(|t| t.kind() == DOT);
    let takes_self = label
        .get(params.first().map_or(0, |p| p.0 as usize)..)
        .is_some_and(|rest| rest.starts_with("self") || rest.starts_with("inout self"));
    if after_dot && takes_self {
        active += 1;
    }
    Some(Signature {
        label,
        params,
        active,
        docs: of.docs(i),
    })
}

/// The name of the function that the call holding `offset` calls, with how many of its
/// arguments come before `offset`.
fn open_call(root: &SyntaxNode, offset: TextSize) -> Option<(SyntaxToken, u32)> {
    let mut token = root.token_at_offset(offset).left_biased()?;
    if token.text_range().start() >= offset {
        token = token.prev_token()?;
    }
    let mut depth = 0u32;
    let mut commas = 0;
    loop {
        match token.kind() {
            R_PAREN | R_BRACK | R_CURLY => depth += 1,
            L_BRACK | L_CURLY | L_PAREN if depth > 0 => depth -= 1,
            L_BRACK | L_CURLY => return None,
            L_PAREN => {
                let name = previous(&token)?;
                return matches!(name.kind(), LOWER_IDENT | UPPER_IDENT).then_some((name, commas));
            }
            COMMA if depth == 0 => commas += 1,
            _ => {}
        }
        token = token.prev_token()?;
    }
}

/// The token before `token` that isn't trivia.
fn previous(token: &SyntaxToken) -> Option<SyntaxToken> {
    let mut t = token.prev_token()?;
    while t.kind().is_trivia() {
        t = t.prev_token()?;
    }
    Some(t)
}

/// The path of the function that `callee` names: as type checking resolved it, or else a
/// method of the type its receiver's binding writes, or a function the module may name.
fn callee_path(
    db: &Database,
    program: Program,
    file: SourceFile,
    callee: &SyntaxToken,
    parts: &mut Parts<'_>,
) -> Option<String> {
    if let Some(Named::Function(path)) = named_at(db, program, file, callee.text_range().start()) {
        return Some(path);
    }
    let name = callee.text();
    let dot = previous(callee).filter(|t| t.kind() == DOT);
    let Some(dot) = dot else {
        let module = stilt_hir::module_hir(db, program, file);
        return [module.name.as_ref(), "std.prelude"]
            .iter()
            .map(|home| format!("{home}.{name}"))
            .find(|p| parts.declaration(p).is_some());
    };
    let receiver = previous(&dot)?;
    let at = receiver.text_range().start();
    let written = written_type(db, program, file, receiver.text(), at)
        .unwrap_or_else(|| receiver.text().to_owned());
    let head = written.split(['<', ' ']).next()?.to_owned();
    if let Some(import) = stilt_hir::module_hir(db, program, file)
        .imports
        .iter()
        .find(|m| m.rsplit('.').next() == Some(head.as_str()))
    {
        return Some(format!("{import}.{name}"));
    }
    let ty = resolve_written(db, program, file, &head, parts)?;
    Some(format!("{ty}.{name}"))
}

/// The spans of a header's parameters: what its parentheses hold, split at the commas outside
/// any bracket.
fn params(label: &str) -> Vec<(u32, u32)> {
    let Some(open) = label.find('(') else {
        return Vec::new();
    };
    let mut found = Vec::new();
    let mut depth = 0i32;
    let mut start = open + 1;
    let bytes = label.as_bytes();
    for (i, &b) in bytes.iter().enumerate().skip(open + 1) {
        match b {
            b'>' if bytes[i - 1] == b'-' => {}
            b'(' | b'[' | b'<' | b'{' => depth += 1,
            b')' if depth == 0 => {
                push(label, start, i, &mut found);
                break;
            }
            b')' | b']' | b'>' | b'}' => depth -= 1,
            b',' if depth == 0 => {
                push(label, start, i, &mut found);
                start = i + 1;
            }
            _ => {}
        }
    }
    found
}

/// Pushes the span from `start` to `end` of `label`, trimmed, if it holds anything.
fn push(label: &str, start: usize, end: usize, found: &mut Vec<(u32, u32)>) {
    let piece = &label[start..end];
    let lead = piece.len() - piece.trim_start().len();
    let trimmed = piece.trim();
    if trimmed.is_empty() {
        return;
    }
    let from = start + lead;
    let byte = |n: usize| u32::try_from(n).unwrap_or(u32::MAX);
    found.push((byte(from), byte(from + trimmed.len())));
}
