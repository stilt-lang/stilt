//! What name resolution asks of procedural macros (macros.procedural-uses), through a [`Host`]
//! that the compiler installs: whether a macro can expand a use, and the run of its body on the
//! use's parts. Resolution splits a use into parts and gives each its parameter; the host checks
//! the macro's module, runs the macro and gives back the tokens of its expansion, each with
//! where it came from, which resolution then places and resolves as code written at the use.
//!
//! Every position a run sees or gives is relative to the start of the use, so that a use that
//! moves gives the same run, and its expansion is computed once (macros.running).

use std::sync::OnceLock;

use stilt_db::{Db, Program, SourceFile};
use stilt_syntax::SyntaxKind;
use stilt_syntax::forms::{Form, FormParse, Piece, parse_form};

use crate::hir::{CodeForm, Input, Name};
use crate::items::{ItemSummary, item_tree};
use crate::scope::def_map;
use crate::scope::view::{Lookup, view_of};

/// The most tokens that the expansions of a use the user wrote hold in all
/// (macros.expansion-size).
pub const EXPANSION_TOKENS: usize = 100_000;

/// What a usable macro takes and gives (macros.procedural-declarations).
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct Signature {
    /// The forms of its parameters, in order.
    pub inputs: Vec<Input>,
    /// The form of the code it gives.
    pub result: CodeForm,
}

/// Whether a macro expands uses: its module, checked with the modules it imports, has no
/// error, and its declaration keeps macros.procedural-declarations (macros.expansion-order).
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub enum State {
    /// It expands uses, as this signature states.
    Usable(Signature),
    /// It expands none.
    Unusable,
}

/// A span relative to the start of a use, in bytes of its file: where the use's tokens are, and
/// where a run places what it reports.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq, Hash)]
pub struct Rel {
    /// Its start.
    pub start: i64,
    /// Its end.
    pub end: i64,
}

impl Rel {
    /// The span from this one's start to `other`'s end, or empty if `other` ends before it starts.
    #[must_use]
    pub fn to(self, other: Rel) -> Rel {
        Rel {
            start: self.start,
            end: other.end.max(self.start),
        }
    }
}

/// A token of a use, as the parser reads it: a separator is `SEP`, with `;` as its text, or an
/// empty text when a newline inserted it.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct Lexeme {
    /// Its kind.
    pub kind: SyntaxKind,
    /// Its text.
    pub text: Name,
    /// Its span.
    pub at: Rel,
}

/// What a use gives one parameter (macros.procedural-uses, macros.tokens-and-code and
/// macros.named-files), its tokens by their indices among the use's lexemes.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub enum Given {
    /// A part that parses whole as code of this form, with no separator at its top level.
    Code(CodeForm, Vec<u32>),
    /// A string literal without interpolation.
    Text(u32),
    /// A string literal that names a file, with the file's text.
    File(u32, String),
    /// The tokens of the parts from one on, or of a trailing block, with no separator that a
    /// newline inserted at their top level, and the span of what ends them.
    Tokens(Vec<u32>, Rel),
}

/// A use of a macro, as its run sees it.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct Call {
    /// The module that declares the macro, and the macro.
    pub home: Name,
    /// The macro's name.
    pub name: Name,
    /// The use's tokens, its brackets included.
    pub lexemes: Vec<Lexeme>,
    /// What it gives each parameter, in order.
    pub given: Vec<Given>,
    /// The use's own span, where the code that quotes write is placed.
    pub at: Rel,
    /// The form its expansion stands as, which the expansion is parsed as.
    pub form: Form,
}

/// Where a token of an expansion came from.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub enum Origin {
    /// The use's token of this index, spliced as code or as a name: the user's.
    Given(u32),
    /// A token that a quote of the module `home` wrote, whose names resolve there, the quote's
    /// evaluation numbered `id` in the run: the names that one evaluation binds are its own
    /// (macros.quote-hygiene).
    Quote {
        /// The module whose items its names resolve among.
        home: Name,
        /// The number of the quote's evaluation in the run.
        id: u32,
    },
    /// A fresh name, by its number in the run (macros.tokens-and-code).
    Fresh(u32),
    /// A token placed at a span of the use's file: a literal a splice wrote, at the use, or a
    /// token of a file a use names, at the literal that names it, which is the user's.
    Placed {
        /// The span.
        at: Rel,
        /// Whether the token is the user's.
        user: bool,
    },
}

/// A token of an expansion.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct OutTok {
    /// Its kind, as the parser reads it.
    pub kind: SyntaxKind,
    /// Its text.
    pub text: Name,
    /// Where it came from.
    pub origin: Origin,
}

/// A place a raised error names: a span of the use's file, or of a file a use names, which is
/// reported at the literal that names it, with the file's line and column (macros.raised-errors).
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct Place {
    /// The span in the use's file.
    pub at: Rel,
    /// In a named file: its line and column there.
    pub in_file: Option<(u32, u32)>,
}

/// How a run ends (macros.running, macros.raised-errors and macros.step-limits).
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub enum Outcome {
    /// The expansion's tokens, their parse as the use's form ([`parsed`]), and the text of the
    /// quote that wrote its code, which a note shows.
    Expanded {
        /// The expansion's tokens.
        tokens: Vec<OutTok>,
        /// Their parse as the use's form.
        parsed: FormParse,
        /// The text of the quote that wrote its code.
        quote: String,
    },
    /// The macro raised an error: its place, its message and its notes.
    Raised {
        /// The place the error names.
        at: Place,
        /// Its message.
        message: String,
        /// Its notes, each at its place.
        notes: Vec<(Place, String)>,
    },
    /// The run stopped, for this reason (macros.step-limits).
    Stopped(String),
    /// The run gave code of this many tokens, more than [`EXPANSION_TOKENS`], which no
    /// expansion holds, and so isn't parsed (macros.expansion-size).
    TooLarge(usize),
}

/// What runs procedural macros.
pub trait Host: Send + Sync {
    /// Whether the macro `name` of module `home` expands uses in `program`.
    fn state(&self, db: &dyn Db, program: Program, home: Name, name: Name) -> State;
    /// The run of a usable macro on a use in `program`, which the host keeps for the next use
    /// that gives the same call.
    fn run<'db>(&self, db: &'db dyn Db, program: Program, call: Call) -> &'db Outcome;
}

/// The parse of an expansion's tokens as the form `call` stands as, each token of the use as
/// resolution places it, a separator that a newline inserted being `;`, and every other as the
/// run wrote it, so that its tree and the positions of its tokens are those of the tokens that
/// resolution places (macros.running).
#[must_use]
pub fn parsed(call: &Call, tokens: &[OutTok]) -> FormParse {
    let pieces: Vec<Piece<'_>> = tokens
        .iter()
        .map(|t| match t.origin {
            Origin::Given(i) => match call.lexemes.get(i as usize) {
                Some(l) if l.kind == SyntaxKind::SEP => Piece {
                    kind: l.kind,
                    text: ";",
                },
                Some(l) => Piece {
                    kind: l.kind,
                    text: l.text.as_str(),
                },
                None => Piece {
                    kind: t.kind,
                    text: t.text.as_str(),
                },
            },
            _ => Piece {
                kind: t.kind,
                text: t.text.as_str(),
            },
        })
        .collect();
    parse_form(&pieces, call.form)
}

static HOST: OnceLock<Box<dyn Host>> = OnceLock::new();

/// Installs the host that runs procedural macros in this process. Without one, no macro
/// expands a use.
pub fn install(host: Box<dyn Host>) {
    let _ = HOST.set(host);
}

pub(crate) fn host() -> Option<&'static dyn Host> {
    HOST.get().map(|h| &**h)
}

/// The modules of a program that a module imports, with `use` and `meta use`, and theirs, the
/// module itself first: those that checking it reads, which a program of their own holds
/// (macros.expansion-order). The standard library's are every program's.
#[salsa::tracked(returns(ref))]
pub fn closure(db: &dyn Db, program: Program, home: Name) -> Vec<SourceFile> {
    let map = def_map(db, program);
    let mut seen: Vec<SourceFile> = Vec::new();
    let mut names = vec![home];
    let mut todo = vec![home];
    while let Some(name) = todo.pop() {
        let Some(m) = map.module(&name).filter(|m| !m.std) else {
            continue;
        };
        if seen.contains(&m.file) {
            continue;
        }
        seen.push(m.file);
        let view = view_of(db, program, m.file);
        for item in &item_tree(db, m.file).items {
            let (ItemSummary::Use(path) | ItemSummary::MetaUse(path)) = item else {
                continue;
            };
            let written: Vec<&str> = path.iter().map(|n| &**n).collect();
            if let Lookup::Found(ns) = view.lookup(map, &written.join("."))
                && !names.contains(&ns)
            {
                names.push(ns);
                todo.push(ns);
            }
        }
    }
    seen
}

/// Whether module `user` is among those that checking module `home` reads: a cycle through
/// `meta use`, which E0206 reports, so that `home`'s macros don't expand there.
pub(crate) fn reaches(db: &dyn Db, program: Program, home: Name, user: SourceFile) -> bool {
    closure(db, program, home).contains(&user)
}

/// The text of the file `path` that a use in `file` names (macros.named-files), or why it can't be
/// read.
pub(crate) fn read_file(
    db: &dyn Db,
    program: Program,
    file: SourceFile,
    path: &str,
) -> Result<String, stilt_db::Unread> {
    let package = stilt_db::package_of(db, program, file);
    let dir = program
        .packages(db)
        .list
        .get(package)
        .and_then(|p| p.dir.clone());
    let Some(dir) = dir else {
        return Err(stilt_db::Unread {
            why: format!("`{path}` can't be read: the program has no directory"),
            meant: None,
        });
    };
    stilt_db::named_file(db, &dir, path).read(db).clone()
}
