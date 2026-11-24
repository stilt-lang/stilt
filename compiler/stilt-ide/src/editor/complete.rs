//! Completion: what may be written at a position, which is often in code that doesn't parse
//! yet, so the position's context is read off the text. After `use`, the modules of the
//! program and of the standard library; after a `.`, the members of what it follows; and
//! elsewhere the variables in scope, the items the module may name, and the keywords that may
//! stand there. A `.` that ends a line leaves its function with a syntax error and no types,
//! so the engine checks the file once more with the `.` and what follows it taken out
//! ([`Completed::Patch`]), to find the type of what the `.` follows.

use stilt_db::{Database, Program, SourceFile};
use stilt_lsp::{Completion, Sort};
use stilt_syntax::{TextRange, TextSize};

use super::members::{Receiver, of_type};
use super::scope::{self, items, locals, module_items};
use super::snippets;
use super::typed;
use crate::show::lookup::Parts;
use crate::show::position::resolve_written;

/// The keywords that start an item.
const ITEM_KEYWORDS: [&str; 11] = [
    "fn", "type", "trait", "impl", "const", "test", "use", "pub", "module", "syntax", "effect",
];

/// The keywords that start a statement or an expression in a body.
const BODY_KEYWORDS: [&str; 25] = [
    "let", "var", "if", "else", "match", "for", "in", "while", "loop", "return", "break",
    "continue", "raise", "try", "catch", "assert", "yield", "true", "false", "self", "handler",
    "with", "resume", "when", "comptime",
];

/// What completion found, or the text to check again first.
#[derive(Debug)]
pub enum Completed {
    /// The completions found.
    Done(Vec<Completion>),
    /// The file, with the `.` and the word after it taken out, in which the receiver, at the
    /// same place, may have a type.
    Patch {
        /// The file's text without them.
        text: String,
        /// Where the receiver is in that text.
        receiver: TextRange,
    },
}

/// What may be written at `offset` of `file`.
pub fn completion(db: &Database, program: Program, file: SourceFile, offset: u32) -> Completed {
    let text = crate::text(db, file);
    let at = (offset as usize).min(text.len());
    let word = word_start(&text, at);
    if let Some(prefix) = use_prefix(&text, word) {
        return Completed::Done(modules(db, program, &prefix));
    }
    if word > 0 && text.as_bytes()[word - 1] == b'.' {
        let Some(receiver) = receiver(&text, word - 1) else {
            return Completed::Done(Vec::new());
        };
        if let Some(found) = statics(db, program, file, &text[range(receiver)]) {
            return Completed::Done(found);
        }
        if let Some(ty) = value_type(db, program, file, receiver) {
            return Completed::Done(of_type(db, program, file, &ty, Receiver::Value));
        }
        return patch(&text, receiver, end_of_word(&text, at));
    }
    Completed::Done(names(
        db,
        program,
        file,
        TextSize::from(offset),
        &text[..word],
    ))
}

/// The members of what a `.` follows, in the file as checked again: by the type checking
/// found, and otherwise by the type that its binding writes.
pub fn members(
    db: &Database,
    program: Program,
    file: SourceFile,
    receiver: TextRange,
) -> Vec<Completion> {
    let ty = value_type(db, program, file, receiver).or_else(|| {
        let text = crate::text(db, file);
        let name = &text[range(receiver)];
        let written = scope::written_type(db, program, file, name, receiver.start())?;
        let head = head_of(&written)?;
        resolve_written(db, program, file, &head, &mut Parts::new(db, program))
    });
    ty.map(|ty| of_type(db, program, file, &ty, Receiver::Value))
        .unwrap_or_default()
}

/// The text to check again for the type of the receiver of a `.` that ends at `end`: without
/// the `.` and the word after it, and, for a line that holds nothing else, with the receiver
/// bound to `_`, so that the block around it keeps its type.
fn patch(text: &str, receiver: TextRange, end: usize) -> Completed {
    let (start, dot) = (usize::from(receiver.start()), usize::from(receiver.end()));
    let line_start = text[..start].rfind('\n').map_or(0, |n| n + 1);
    let line_end = text[end..].find('\n').map_or(text.len(), |n| end + n);
    let alone = text[line_start..start].trim().is_empty() && text[end..line_end].trim().is_empty();
    let lead = if alone { "let _ = " } else { "" };
    let mut patched = String::with_capacity(text.len() + lead.len());
    patched.push_str(&text[..start]);
    patched.push_str(lead);
    patched.push_str(&text[start..dot]);
    patched.push_str(&text[end..]);
    let shift = TextSize::from(u32::try_from(lead.len()).unwrap_or(0));
    Completed::Patch {
        text: patched,
        receiver: receiver + shift,
    }
}

fn range(r: TextRange) -> std::ops::Range<usize> {
    usize::from(r.start())..usize::from(r.end())
}

/// The type of the receiver at `receiver`, as type checking found it.
fn value_type(
    db: &Database,
    program: Program,
    file: SourceFile,
    receiver: TextRange,
) -> Option<String> {
    typed::head(typed::node_at(db, program, file, receiver)?.ty())
}

/// The members of a module or a type that a `.` follows, if `written` names one: a module's
/// `pub` items, or a type's variants and functions without `self`.
fn statics(
    db: &Database,
    program: Program,
    file: SourceFile,
    written: &str,
) -> Option<Vec<Completion>> {
    let module = stilt_hir::module_hir(db, program, file);
    if let Some(import) = module
        .imports
        .iter()
        .find(|m| m.rsplit('.').next() == Some(written))
    {
        return Some(module_items(db, program, import));
    }
    let last = written.rsplit('.').next().unwrap_or(written);
    if !last.starts_with(char::is_uppercase) {
        return None;
    }
    let ty = resolve_written(db, program, file, written, &mut Parts::new(db, program));
    let reflects = &*module.name == "std.meta" || module.imports.iter().any(|m| &**m == "std.meta");
    if ty.is_none() && !reflects {
        return None;
    }
    let mut found = ty.map_or_else(Vec::new, |ty| {
        of_type(db, program, file, &ty, Receiver::Type)
    });
    if reflects {
        found.extend(reflection(&found));
    }
    Some(found)
}

/// `T.shape()` and `T.name()`, in `std.meta` and a module that names it, after a type's own
/// members of those names, which are found first (meta.shape-and-name).
fn reflection(own: &[Completion]) -> Vec<Completion> {
    [
        (
            "shape",
            "fn() -> meta.Shape<T>",
            "The shape of the type: its case of `meta.Shape`.",
        ),
        (
            "name",
            "fn() -> str",
            "The type's name, as a diagnostic writes it.",
        ),
    ]
    .into_iter()
    .filter(|(label, ..)| !own.iter().any(|c| c.label == *label))
    .map(|(label, detail, docs)| Completion {
        label: label.to_owned(),
        sort: Sort::Function,
        detail: Some(detail.to_owned()),
        docs: Some(docs.to_owned()),
        insert: Some(format!("{label}()$0")),
    })
    .collect()
}

/// The modules whose paths start with `prefix`, each by the rest of its path.
fn modules(db: &Database, program: Program, prefix: &str) -> Vec<Completion> {
    let mut found: Vec<Completion> = Vec::new();
    for &f in program.files(db).iter().chain(program.std(db)) {
        let name = stilt_hir::module_hir(db, program, f).name;
        let Some(rest) = name.strip_prefix(prefix) else {
            continue;
        };
        if rest.is_empty()
            || name.as_ref() == "std.prelude"
            || found.iter().any(|c| c.label == rest)
        {
            continue;
        }
        found.push(Completion {
            label: rest.to_owned(),
            sort: Sort::Module,
            detail: Some(name.to_string()),
            docs: None,
            insert: None,
        });
    }
    found
}

/// The names that may be written at `offset`: the variables in scope with their types, the
/// items, and the keywords, or only the types where a type is written.
fn names(
    db: &Database,
    program: Program,
    file: SourceFile,
    offset: TextSize,
    before: &str,
) -> Vec<Completion> {
    let root = stilt_db::parse(db, file).syntax();
    let in_body = scope::declaration_at(&root, offset).is_some_and(|d| {
        d.children()
            .find(|c| {
                matches!(
                    c.kind(),
                    stilt_syntax::SyntaxKind::BLOCK | stilt_syntax::SyntaxKind::ERROR
                )
            })
            .is_some_and(|b| b.text_range().start() < offset)
    });
    let typing = before.trim_end().ends_with(':') || before.trim_end().ends_with("->");
    let mut found: Vec<Completion> = Vec::new();
    if in_body && !typing {
        found.extend(locals(&root, offset).into_iter().map(|l| {
            let ty = crate::show::position::local_type(db, program, file, l.at.start());
            Completion {
                label: l.name,
                sort: if l.param {
                    Sort::Parameter
                } else {
                    Sort::Local
                },
                detail: ty.or(l.written),
                docs: None,
                insert: None,
            }
        }));
    }
    let wanted = |c: &Completion| {
        !typing
            || matches!(
                c.sort,
                Sort::Type | Sort::Trait | Sort::Effect | Sort::Module
            )
    };
    found.extend(items(db, program, file).into_iter().filter(wanted));
    if typing {
        found.extend(
            stilt_syntax::PRIMITIVE_TYPES
                .iter()
                .map(|t| keyword(t, Sort::Type)),
        );
    } else if in_body {
        found.extend(BODY_KEYWORDS.iter().map(|k| keyword(k, Sort::Keyword)));
    } else {
        found.extend(ITEM_KEYWORDS.iter().map(|k| keyword(k, Sort::Keyword)));
    }
    found
}

/// A keyword, with its construct where it has one, or a primitive type.
fn keyword(word: &str, sort: Sort) -> Completion {
    let insert = snippets::keyword(word).filter(|_| sort == Sort::Keyword);
    Completion {
        label: word.to_owned(),
        sort,
        detail: insert.map(snippets::preview),
        docs: None,
        insert: insert.map(str::to_owned),
    }
}

/// The written type's head, without its arguments, as `List` of `List<i64>`.
fn head_of(written: &str) -> Option<String> {
    let head = written.trim().split(['<', ' ', '/']).next()?;
    (!head.is_empty() && !head.starts_with(['(', '{'])).then(|| head.to_owned())
}

fn is_word_byte(b: u8) -> bool {
    b.is_ascii_alphanumeric() || b == b'_'
}

/// Where the word that ends at `at` starts.
fn word_start(text: &str, at: usize) -> usize {
    let bytes = text.as_bytes();
    let mut start = at;
    while start > 0 && is_word_byte(bytes[start - 1]) {
        start -= 1;
    }
    start
}

/// Where the word that holds `at` ends.
fn end_of_word(text: &str, at: usize) -> usize {
    let bytes = text.as_bytes();
    let mut end = at;
    while end < bytes.len() && is_word_byte(bytes[end]) {
        end += 1;
    }
    end
}

/// The path written after `use` on the line before the word at `word`, as `std.`, if the
/// line is a `use` declaration.
fn use_prefix(text: &str, word: usize) -> Option<String> {
    let line_start = text[..word].rfind('\n').map_or(0, |n| n + 1);
    let rest = text[line_start..word].trim_start().strip_prefix("use ")?;
    let path = rest.trim_start();
    path.bytes()
        .all(|b| is_word_byte(b) || b == b'.')
        .then(|| path.to_owned())
}

/// The span of what the `.` at `dot` follows: names joined by `.`, each maybe followed by
/// bracketed arguments, as `xs.first()` or `self.items[0]`. None after a number.
fn receiver(text: &str, dot: usize) -> Option<TextRange> {
    let bytes = text.as_bytes();
    let mut start = dot;
    loop {
        let mut bracketed = false;
        while start > 0 && matches!(bytes[start - 1], b')' | b']') {
            start = opening(bytes, start - 1)?;
            bracketed = true;
        }
        let end = start;
        start = word_start(text, start);
        if start == end && !bracketed {
            return None;
        }
        if start > 0 && bytes[start - 1] == b'.' {
            start -= 1;
        } else {
            break;
        }
    }
    if bytes[start].is_ascii_digit() {
        return None;
    }
    let offset = |n: usize| TextSize::from(u32::try_from(n).unwrap_or(u32::MAX));
    Some(TextRange::new(offset(start), offset(dot)))
}

/// Where the bracket that the one at `close` closes is.
fn opening(bytes: &[u8], close: usize) -> Option<usize> {
    let mut depth = 0usize;
    for i in (0..=close).rev() {
        match bytes[i] {
            b')' | b']' => depth += 1,
            b'(' | b'[' => {
                depth -= 1;
                if depth == 0 {
                    return Some(i);
                }
            }
            _ => {}
        }
    }
    None
}
