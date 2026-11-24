//! A procedural macro's run on a use (macros.running, macros.raised-errors and macros.step-limits):
//! the values of its parts, the call of the macro on a thread of its own, deep enough for 10,000
//! frames, and how the run ends: the tokens of its expansion, the error it raised, or why it
//! stopped.

use std::collections::HashMap;
use std::sync::Arc;

use stilt_db::{Db, Program};
use stilt_hir::hir::{Item, Name};
use stilt_hir::procs::{Call, Given, OutTok, Outcome, Place, Rel};
use stilt_syntax::text::literal_value;
use stilt_types::tast::Callee;

use crate::eval::{Flow, Machine};
use crate::image::{Image, image};
use crate::limits::Run;
use crate::meta::tokens;
use crate::value::{Code, Meta, Span, Text, TextOrigin, Value, meta_item};

/// The stack of a run's thread: enough for 10,000 frames of the deepest code.
const STACK: usize = 1 << 30;

/// What a run reads of its use, and what it numbers.
#[derive(Debug)]
pub(crate) struct Io<'a> {
    pub(crate) call: &'a Call,
    /// The texts of the files the use names, each with the index of the literal that names it.
    pub(crate) files: Vec<(Arc<str>, u32)>,
    pub(crate) fresh: u32,
    pub(crate) quotes: u32,
    /// The text of the last quote evaluated, which a note shows.
    pub(crate) quote: String,
}

impl<'a> Io<'a> {
    /// What it holds, given to another thread of the run, this one keeping only the use.
    pub(crate) fn take(&mut self) -> Io<'a> {
        Io {
            call: self.call,
            files: std::mem::take(&mut self.files),
            fresh: self.fresh,
            quotes: self.quotes,
            quote: std::mem::take(&mut self.quote),
        }
    }

    /// The span of the literal that names the file `k`.
    pub(crate) fn literal_of(&self, k: u32) -> Rel {
        self.files
            .get(k as usize)
            .and_then(|(_, i)| self.call.lexemes.get(*i as usize))
            .map_or(self.call.at, |l| l.at)
    }

    pub(crate) fn use_rel(&self) -> Rel {
        self.call.at
    }

    pub(crate) fn use_span(&self) -> Span {
        Span {
            start: self.call.at.start,
            end: self.call.at.end,
            file: None,
        }
    }

    fn lexeme_span(&self, i: u32) -> Span {
        let at = self
            .call
            .lexemes
            .get(i as usize)
            .map_or(self.call.at, |l| l.at);
        Span {
            start: at.start,
            end: at.end,
            file: None,
        }
    }

    /// Where a diagnostic at a span is reported: in a named file, at the literal that names it,
    /// with the file's line and column (macros.raised-errors).
    fn place(&self, s: Span) -> Place {
        match s.file {
            Some(k) => {
                let text = self.files.get(k as usize).map_or("", |(t, _)| &**t);
                let upto = usize::try_from(s.start).unwrap_or(0).min(text.len());
                let before = &text[..upto];
                let line = before.matches('\n').count() + 1;
                let col = before.rsplit('\n').next().map_or(0, |l| l.chars().count()) + 1;
                Place {
                    at: self.literal_of(k),
                    in_file: Some((
                        u32::try_from(line).unwrap_or(u32::MAX),
                        u32::try_from(col).unwrap_or(u32::MAX),
                    )),
                }
            }
            None => Place {
                at: Rel {
                    start: s.start,
                    end: s.end,
                },
                in_file: None,
            },
        }
    }
}

/// Runs the macro of `call` in `program`, the program of its module: on a thread of its own, or
/// on WebAssembly, which runs one thread, as the playground's compiler does, on the caller's.
pub(crate) fn run(db: &dyn Db, program: Program, call: &Call) -> Outcome {
    let item = Item {
        home: call.home,
        name: call.name,
    };
    let image = image(db, program, &item);
    if cfg!(target_os = "wasi") {
        return run_image(&image, call, item);
    }
    std::thread::scope(|s| {
        let spawned = std::thread::Builder::new()
            .name("macro".to_owned())
            .stack_size(STACK)
            .spawn_scoped(s, || run_image(&image, call, item.clone()));
        match spawned.map(std::thread::ScopedJoinHandle::join) {
            Ok(Ok(outcome)) => outcome,
            Ok(Err(panic)) => std::panic::resume_unwind(panic),
            Err(_) => Outcome::Stopped("it ran out of stack".to_owned()),
        }
    })
}

fn run_image(image: &Image<'_>, call: &Call, item: Item) -> Outcome {
    crate::value::use_meter(&std::sync::Arc::new(std::sync::atomic::AtomicUsize::new(0)));
    let mut m = Machine {
        image,
        run: Run::new(call.home),
        io: Io {
            call,
            files: Vec::new(),
            fresh: 0,
            quotes: 0,
            quote: String::new(),
        },
        constants: HashMap::new(),
        fx: crate::fiber::Effects::default(),
        escaped: None,
        pool: crate::frame::Pool::default(),
    };
    let mut args: Vec<Value<'_>> = call.given.iter().map(|g| argument(&mut m.io, g)).collect();
    let callee = Callee::Function(item);
    let result = match m.target_in((&[], None), &callee, &[], &args) {
        Ok(target) => m.apply(target, &mut args),
        Err(flow) => Err(flow),
    };
    match result {
        Ok(Value::Meta(meta)) => match &*meta {
            Meta::Code(c) => expanded(call, c, std::mem::take(&mut m.io.quote)),
            _ => unreachable!("a macro gives code of its result's form, as checking found"),
        },
        Err(Flow::Raise(Value::Meta(meta))) => match &*meta {
            Meta::Error(e) => Outcome::Raised {
                at: m.io.place(e.at),
                message: e.message.clone(),
                notes: e
                    .notes
                    .iter()
                    .map(|(s, t)| (m.io.place(*s), t.clone()))
                    .collect(),
            },
            _ => {
                unreachable!(
                    "a macro raises only `meta.Error`, as checking found (macros.procedural-declarations)"
                )
            }
        },
        Err(Flow::Stop(stop)) => {
            Outcome::Stopped(format!("{}{}", stop.reason(), m.run.shown_frames()))
        }
        Ok(_) => unreachable!("a macro gives code of its result's form, as checking found"),
        Err(Flow::Raise(_)) => {
            unreachable!(
                "a macro raises only `meta.Error`, as checking found (macros.procedural-declarations)"
            )
        }
        Err(Flow::Return(_) | Flow::Break | Flow::Continue | Flow::Abandon) => unreachable!(
            "a body's run ends with its value, a raise or a stop: its `return`, `break`, \
             `continue` and dropped blocks end inside it"
        ),
    }
}

/// The expansion a run gave, with its parse, which the run's query keeps with it, or its size
/// when it holds more tokens than any expansion may (macros.expansion-size).
fn expanded(call: &Call, c: &Code, quote: String) -> Outcome {
    if c.tokens.len() > stilt_hir::procs::EXPANSION_TOKENS {
        return Outcome::TooLarge(c.tokens.len());
    }
    let tokens: Vec<OutTok> = c
        .tokens
        .iter()
        .map(|l| OutTok {
            kind: l.kind,
            text: l.text,
            origin: l.origin.clone(),
        })
        .collect();
    Outcome::Expanded {
        parsed: stilt_hir::procs::parsed(call, &tokens),
        tokens,
        quote,
    }
}

/// The value a use gives a parameter (macros.tokens-and-code).
fn argument<'a>(io: &mut Io<'_>, g: &Given) -> Value<'a> {
    match g {
        Given::Code(form, indices) => {
            let raws = tokens::given(io, indices);
            let span = match (raws.first(), raws.last()) {
                (Some(a), Some(b)) => a.span.to(b.span),
                _ => io.use_span(),
            };
            Value::meta(Meta::Code(Code {
                tokens: Arc::new(crate::value::Counted::new(
                    raws.into_iter().map(|r| r.lex).collect(),
                )),
                span,
                form: *form,
            }))
        }
        Given::Text(i) => Value::meta(Meta::Text(literal(io, *i))),
        Given::File(i, contents) => {
            let k = u32::try_from(io.files.len()).unwrap_or(u32::MAX);
            io.files.push((Arc::from(contents.as_str()), *i));
            let path = literal(io, *i).value;
            let text = Text {
                value: Arc::from(contents.as_str()),
                origin: TextOrigin::File(k),
            };
            Value::record(
                meta_item("File"),
                vec![
                    (Name::from("path"), Value::str(&*path)),
                    (Name::from("text"), Value::meta(Meta::Text(text))),
                    (
                        Name::from("span"),
                        Value::meta(Meta::Span(io.lexeme_span(*i))),
                    ),
                ],
            )
        }
        Given::Tokens(indices, close) => {
            let raws = tokens::given(io, indices);
            let close = Span {
                start: close.start,
                end: close.end,
                file: None,
            };
            tokens::record(&tokens::tree(&raws), close)
        }
    }
}

/// The text of the string literal of the use's token `i`.
fn literal(io: &Io<'_>, i: u32) -> Text {
    let raw = io.call.lexemes.get(i as usize).map_or("", |l| &*l.text);
    Text {
        value: Arc::from(literal_value(raw).as_str()),
        origin: TextOrigin::Literal {
            raw: Arc::from(raw),
            at: io.lexeme_span(i),
        },
    }
}
