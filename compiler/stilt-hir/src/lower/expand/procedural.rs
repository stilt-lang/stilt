//! The uses of procedural macros (macros.meta-use, macros.procedural-uses and macros.running): a
//! use whose path is a name that `meta use` binds and a macro of that module is split into parts,
//! given to the macro's run, and replaced by the tokens it gives back, each placed where it came
//! from: a token of the use where the user wrote it, a quote's own at the use, marked so that its
//! names resolve in the quote's module (macros.quote-hygiene), and a fresh name marked as a name of
//! its own.

use rustc_hash::FxHashMap;
use stilt_diag::{Diagnostic, codes};
use stilt_syntax::ast::{self, AstNode, MacroElem};
use stilt_syntax::forms::{Form, FormParse};
use stilt_syntax::{SyntaxKind, TextRange, TextSize};

use super::parts::UseTok;
use super::{MAX_DEPTH, Made, path_span};
use crate::hir::{CodeForm, Ident, Name, Template};
use crate::lower::Resolver;
use crate::macros::bracket_text;
use crate::macros::substitute::Tok;
use crate::procs::{
    Call, Lexeme, Origin, OutTok, Outcome, Place, Rel, Signature, State, host, reaches,
};
use crate::scope::{Kind, Namespace};

/// Where a use's group's brackets are among its tokens, and its trailing block's, if it has one.
pub(super) type Brackets = ((usize, usize), Option<(usize, usize)>);

/// What a use's path names.
pub(super) enum Found {
    /// No procedural macro: a pattern macro's path, resolved as one.
    NotProc,
    /// A procedural macro that gives no expansion here, for a reason reported or not.
    Failed,
    Made(Box<Made>),
}

/// The form of code a macro gives.
fn form_of(result: CodeForm) -> Form {
    match result {
        CodeForm::Expr | CodeForm::Field => Form::Expr,
        CodeForm::Pattern => Form::Pattern,
        CodeForm::Type => Form::Type,
    }
}

fn form_name(form: Form) -> &'static str {
    match form {
        Form::Pattern => "a pattern",
        Form::Type => "a type",
        Form::Expr | Form::Block => "an expression",
    }
}

impl Resolver<'_> {
    /// The procedural macro a use's path names through `meta use`, if it names one
    /// (macros.meta-use).
    fn proc_named(&mut self, path: &[Ident]) -> Result<Option<(Name, Ident)>, ()> {
        let [alias, n] = path else { return Ok(None) };
        let (_, scope) = self.home(alias.at);
        let Some(&ns) = scope.metas.get(&alias.name) else {
            return Ok(None);
        };
        match self
            .named_in(&ns, &n.name)
            .and_then(|named| named.find(Namespace::Values))
        {
            Some(e) if e.kind == Kind::Proc && e.is_pub => Ok(Some((ns, n.clone()))),
            Some(e) if e.kind == Kind::Proc => {
                let message = format!("`{ns}.{}` is private to module `{ns}`", n.name);
                self.error(codes::E0213, n.at, message);
                Err(())
            }
            _ if scope.values.contains_key(&alias.name) => Ok(None),
            _ => {
                let message = format!("module `{ns}` has no procedural macro `{}`", n.name);
                let d = Diagnostic::new(codes::E0211, n.at, message);
                self.unknown_name(format!("{}.{}", alias.name, n.name), d);
                Err(())
            }
        }
    }

    /// The expansion of a use whose path may name a procedural macro, standing where `form`
    /// does.
    pub(super) fn procedural(
        &mut self,
        path: &[Ident],
        groups: &[ast::MacroGroup],
        at: TextRange,
        form: Form,
    ) -> Found {
        let (home, macro_name) = match self.proc_named(path) {
            Ok(Some(found)) => found,
            Ok(None) => return Found::NotProc,
            Err(()) => return Found::Failed,
        };
        if self.checking {
            return Found::Failed;
        }
        let Some(signature) = self.proc_signature(home, macro_name.name) else {
            return Found::Failed;
        };
        let name = Name::from(super::super::dotted(path));
        let (path_at, _) = self.placed(path_span(path));
        let (use_at, _) = self.placed(at);
        if !self.proc_fits(name, signature.result, form, (path_at, use_at)) {
            return Found::Failed;
        }
        let (tokens, brackets) = self.proc_tokens(groups);
        let start = use_at.start();
        let mut given = match super::parts::given((&signature.inputs, start), &tokens, brackets) {
            Ok(given) => given,
            Err((at, why, fix)) => {
                let message = format!("`{name}!` can't take this use: {why}");
                let d = Diagnostic::new(codes::E0227, at, message);
                self.diagnostics
                    .push(fix.into_iter().fold(d, Diagnostic::with_fix));
                return Found::Failed;
            }
        };
        if !self.read_files(&tokens, &mut given) {
            return Found::Failed;
        }
        let call = Call {
            home,
            name: macro_name.name,
            lexemes: lexemes(&tokens, start),
            given,
            at: relative(start, use_at),
            form,
        };
        let Some(h) = host() else {
            return Found::Failed;
        };
        let outcome = h.run(self.db, self.program, call);
        self.outcome((name, home), &tokens, outcome, (path_at, use_at), form)
    }

    /// The expansion of a run's `outcome` on the use of `name!` whose tokens are `given`, or
    /// none, after its error (macros.running, macros.raised-errors, macros.step-limits and
    /// macros.expansion-size).
    fn outcome(
        &mut self,
        (name, home): (Name, Name),
        given: &[UseTok],
        outcome: &Outcome,
        (path_at, use_at): (TextRange, TextRange),
        form: Form,
    ) -> Found {
        match outcome {
            Outcome::Expanded {
                tokens: made,
                parsed,
                quote,
            } => self.placed_expansion((name, home), given, (made, parsed, quote), use_at, form),
            Outcome::Raised { at, message, notes } => {
                self.raised(name, use_at.start(), (at, message, notes), path_at);
                Found::Failed
            }
            Outcome::Stopped(reason) => {
                let message = format!("`{name}!` didn't finish: {reason}");
                self.error(codes::E0226, use_at, message);
                Found::Failed
            }
            Outcome::TooLarge(tokens) => {
                self.spend(*tokens, name, use_at);
                Found::Failed
            }
        }
    }

    /// The signature of the macro `name` of module `home`, when the host can run it: its module
    /// has no error and doesn't reach the module of the use, whose checking it would need
    /// (macros.expansion-order).
    fn proc_signature(&self, home: Name, name: Name) -> Option<Signature> {
        let h = host()?;
        if reaches(self.db, self.program, home, self.module.file) {
            return None;
        }
        match h.state(self.db, self.program, home, name) {
            State::Usable(signature) => Some(signature),
            State::Unusable => None,
        }
    }

    /// Whether a macro that gives `result` may stand where `form` does, and its use is nested in
    /// fewer than 128 expansions, or E0223 or E0224 (macros.procedural-uses and
    /// macros.nested-expansions).
    fn proc_fits(
        &mut self,
        name: Name,
        result: CodeForm,
        form: Form,
        (path_at, use_at): (TextRange, TextRange),
    ) -> bool {
        let gives = form_of(result);
        if gives != form {
            let message = format!(
                "`{name}!` stands where {} does, but it gives {}",
                form_name(form),
                form_name(gives)
            );
            self.error(codes::E0223, path_at, message);
            return false;
        }
        if self.regions.len() >= MAX_DEPTH {
            self.too_deep(name, use_at);
            return false;
        }
        true
    }

    /// The tokens of a use's groups, brackets included, each with whether a newline inserted
    /// it, and where the group's brackets and the trailing block's are.
    fn proc_tokens(&self, groups: &[ast::MacroGroup]) -> (Vec<UseTok>, Brackets) {
        let mut out = Vec::new();
        let mut brackets = Vec::new();
        for g in groups {
            let open = out.len();
            self.proc_group(g, &mut out);
            brackets.push((open, out.len() - 1));
        }
        let group = brackets.first().copied().unwrap_or((0, 0));
        (out, (group, brackets.get(1).copied()))
    }

    fn proc_group(&self, g: &ast::MacroGroup, out: &mut Vec<UseTok>) {
        let fallback = self.in_file(g.syntax().text_range());
        let plain = |tok| UseTok {
            tok,
            inserted: false,
        };
        let (open_kind, open_text) = bracket_text(g.bracket(), true);
        out.push(plain(match g.open() {
            Some(t) => self.tok(&t),
            None => self.made(open_kind, open_text, fallback),
        }));
        for e in g.elements() {
            match e {
                MacroElem::Token(t) => out.push(plain(self.tok(&t))),
                MacroElem::Sep(s) => {
                    let at = self.in_file(s.syntax().text_range());
                    out.push(UseTok {
                        tok: self.made(SyntaxKind::SEP, ";", at),
                        inserted: !s.syntax().text().contains_char(';'),
                    });
                }
                MacroElem::Group(inner) => self.proc_group(&inner, out),
                // A use holds no fragment or repetition, and its file then has a syntax error.
                MacroElem::Frag(f) => out.push(plain(self.made(
                    SyntaxKind::DOLLAR,
                    "$",
                    self.in_file(f.syntax().text_range()),
                ))),
                MacroElem::Rep(r) => out.push(plain(self.made(
                    SyntaxKind::DOLLAR,
                    "$",
                    self.in_file(r.syntax().text_range()),
                ))),
            }
        }
        let (close_kind, close_text) = bracket_text(g.bracket(), false);
        out.push(plain(match g.close() {
            Some(t) => self.tok(&t),
            None => self.made(close_kind, close_text, TextRange::empty(fallback.end())),
        }));
    }

    /// The expansion a run gave, its tokens placed, with their parse as `form`, which the run
    /// keeps with it, so that a use that gives the same call parses nothing again.
    fn placed_expansion(
        &mut self,
        (name, home): (Name, Name),
        given: &[UseTok],
        (made, parsed, quote): (&[OutTok], &FormParse, &str),
        use_at: TextRange,
        form: Form,
    ) -> Found {
        let start = use_at.start();
        let mut marks: Vec<(u32, Name)> = Vec::new();
        let mut quotes: FxHashMap<u32, u32> = FxHashMap::default();
        let mut fresh: FxHashMap<u32, u32> = FxHashMap::default();
        let mut tokens = Vec::with_capacity(made.len());
        for t in made {
            let own = |mark| Tok {
                kind: t.kind,
                text: t.text,
                at: use_at,
                user: false,
                mark,
            };
            let tok = match t.origin {
                Origin::Given(i) => given[i as usize].tok.clone(),
                Origin::Quote { home: module, id } => {
                    let mark = *quotes.entry(id).or_insert_with(|| {
                        self.marks += 1;
                        marks.push((self.marks, module));
                        self.marks
                    });
                    own(mark)
                }
                Origin::Fresh(id) => {
                    let mark = *fresh.entry(id).or_insert_with(|| {
                        self.marks += 1;
                        marks.push((self.marks, home));
                        self.marks
                    });
                    own(mark)
                }
                Origin::Placed { at, user } => Tok {
                    kind: t.kind,
                    text: t.text,
                    at: absolute(start, at),
                    user,
                    mark: 0,
                },
            };
            tokens.push(tok);
        }
        if !parsed.is_whole(tokens.len()) {
            let message = format!("the expansion of `{name}!` here doesn't parse");
            self.error(codes::E0100, use_at, message);
            return Found::Failed;
        }
        Found::Made(Box::new(Made {
            parsed: parsed.clone(),
            tokens,
            marks,
            name,
            at: use_at,
            template: Template::Elsewhere(quote.to_owned()),
            form,
            procedural: true,
        }))
    }

    /// E0225 for an error a macro raised, at its span, with its notes and one that names the
    /// macro (macros.raised-errors).
    fn raised(
        &mut self,
        name: Name,
        start: TextSize,
        (at, message, notes): (&Place, &str, &[(Place, String)]),
        path_at: TextRange,
    ) {
        let in_file = |place: &Place, text: &str| match place.in_file {
            Some((line, col)) => format!("{text} (at {line}:{col} of the file)"),
            None => text.to_owned(),
        };
        let mut d = Diagnostic::new(codes::E0225, absolute(start, at.at), in_file(at, message));
        for (place, text) in notes {
            d = d.with_note(absolute(start, place.at), in_file(place, text));
        }
        d = d.with_note(path_at, format!("raised by `{name}!`"));
        self.diagnostics.push(d);
    }
}

/// The tokens of a use as its call gives them, each placed relative to the use, and a
/// separator that a newline inserted without its text (macros.tokens-and-code).
fn lexemes(tokens: &[UseTok], start: TextSize) -> Vec<Lexeme> {
    tokens
        .iter()
        .map(|t| Lexeme {
            kind: t.tok.kind,
            text: if t.inserted {
                Name::from("")
            } else {
                t.tok.text
            },
            at: relative(start, t.tok.at),
        })
        .collect()
}

/// A span of the file, relative to a use that starts at `start`.
pub(super) fn relative(start: TextSize, at: TextRange) -> Rel {
    let from = i64::from(u32::from(start));
    Rel {
        start: i64::from(u32::from(at.start())) - from,
        end: i64::from(u32::from(at.end())) - from,
    }
}

/// A span relative to a use that starts at `start`, in the file.
fn absolute(start: TextSize, at: Rel) -> TextRange {
    let from = i64::from(u32::from(start));
    let point = |x: i64| TextSize::from(u32::try_from((from + x).max(0)).unwrap_or(u32::MAX));
    let (s, e) = (point(at.start), point(at.end.max(at.start)));
    TextRange::new(s, e)
}
