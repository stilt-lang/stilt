//! Effects: the rows that code performs, fitted into the rows that must hold them
//! (effects.inference and effects.missing-effects).

use stilt_diag::{Alternative, AlternativeKind, Code, Fix, codes};
use stilt_syntax::TextRange;

use super::{Cx, State};
use crate::ty::{Handled, Row, RowParam, Ty};
use crate::unify::Problem::{self, self as P};

/// The help of a raise that the row doesn't declare.
const RAISE_HELP: &str = "The error goes on to the function's callers, so its row declares it \
                          with `raise<E>`, and the call is marked with `try`. A `catch` after \
                          the call handles the error there instead.";

/// The help of an effect in a procedural macro's body, whose row can't declare one
/// (macros.procedural-bodies).
const MACRO_HELP: &str = "A macro runs while the program compiles, and performs nothing. Put \
                          what it would perform in the code it gives back, inside `quote { … }`.";

/// The help of a raise of `meta.Error` in a procedural macro's body whose row doesn't declare it.
const MACRO_ERROR_HELP: &str = "A macro's `meta.Error` stops the compile at the use, and the \
                                macro's row declares it with `raise<meta.Error>`.";

/// The help of a raise in a procedural macro's body of another error than `meta.Error`, the only
/// one its row can declare (macros.procedural-declarations).
const MACRO_RAISE_HELP: &str = "A macro raises only `meta.Error`, which stops the compile at \
                                the use: `raise meta.error(span, message)`. Catch the other \
                                error and raise one of those.";

/// Whether a type is `std.meta`'s `Error`, the one error a procedural macro raises.
fn is_meta_error(t: &Ty) -> bool {
    matches!(t, Ty::Con(item, _) if &*item.home == "std.meta" && &*item.name == "Error")
}

/// The kinds of problem a row has reported, so that each is reported once
/// (effects.missing-effects). Each row that effects are fitted into has its own.
#[derive(Default)]
pub(super) struct Reported(Vec<String>);

impl Cx {
    pub(super) fn perform(&mut self, row: Row, at: TextRange) {
        self.effects.push((row, at));
    }
}

impl State<'_> {
    /// Performs the row of a call at `at`, which a `try` around it marks (effects.marking).
    pub(super) fn perform_call(&mut self, cx: &mut Cx, row: Row, at: TextRange) {
        self.unmarked.push(at);
        cx.perform(row, at);
    }
}

impl State<'_> {
    /// Reports what a row can't hold, each kind of problem once. In the function's own row,
    /// `own`, a missing effect is fixed by declaring it.
    pub(super) fn report(
        &mut self,
        reported: &mut Reported,
        (at, own): (TextRange, bool),
        problems: Vec<Problem>,
    ) {
        self.report_in(reported, (at, own, false), problems);
    }

    /// [`State::report`], where a user-defined effect that reaches the row is E0512 if
    /// `unhandled`, as in `main`, a test and a doc example (handlers.no-effect-reaches-main).
    pub(super) fn report_in(
        &mut self,
        reported: &mut Reported,
        (at, own, unhandled): (TextRange, bool, bool),
        problems: Vec<Problem>,
    ) {
        for problem in problems {
            let mut fix = None;
            // In a procedural macro's body, the help says why the row can't declare the effect.
            let mut help = self.env.procedural.then_some(MACRO_HELP);
            let (key, code, message) = match problem {
                p @ (P::MissingEffect(_) | P::EffectMismatch(..)) => self.effects(p, unhandled),
                Problem::MissingIo => {
                    fix = (own && !self.env.procedural)
                        .then(|| self.row_fix("io", true))
                        .flatten();
                    (
                        "io".to_owned(),
                        codes::E0502,
                        "this performs `io`, which the row doesn't declare".to_owned(),
                    )
                }
                Problem::MissingRaise(t) => {
                    let (raise, raise_help, raise_fix) = self.missing_raise(&t, (at, own));
                    (help, fix) = (Some(raise_help), raise_fix);
                    raise
                }
                Problem::MissingVar(p) => {
                    let name = self.row_param_name(&p);
                    (
                        format!("var {name}"),
                        codes::E0502,
                        format!("this performs `{name}`, which the row doesn't declare"),
                    )
                }
                Problem::RaiseMismatch(u, t) => (
                    "raise type".to_owned(),
                    codes::E0503,
                    format!(
                        "this raises `{}`, but the same code raises `{}`",
                        self.show(&u),
                        self.show(&t)
                    ),
                ),
                Problem::CyclicRaise(t) => {
                    self.cyclic_raise(&t, at);
                    continue;
                }
            };
            if !reported.0.contains(&key) {
                let help = help.filter(|_| code == codes::E0502);
                reported.0.push(key);
                self.error_fixed(code, at, message, fix.into_iter().collect());
                if let Some(help) = help {
                    let d = self.errors.pop().map(|d| d.with_help(help));
                    self.errors.extend(d);
                }
            }
        }
    }

    /// The key, code and message of a raise of `t` that the row doesn't declare, with its help
    /// and its fix, which declares it in the function's own row if `own` and the row can hold
    /// it: a procedural macro's holds only `meta.Error` (macros.procedural-declarations).
    fn missing_raise(
        &self,
        t: &Ty,
        (at, own): (TextRange, bool),
    ) -> ((String, Code, String), &'static str, Option<Fix>) {
        let effect = self.written(t).map(|t| format!("raise<{t}>"));
        let declarable = !self.env.procedural || is_meta_error(self.table.resolve(t));
        let help = match (self.env.procedural, declarable) {
            (false, _) => RAISE_HELP,
            (true, true) => MACRO_ERROR_HELP,
            (true, false) => MACRO_RAISE_HELP,
        };
        let fix = effect
            .filter(|_| own && declarable)
            .and_then(|e| self.raise_fix(&e, at));
        let message = format!(
            "this raises `{}`, which the row doesn't declare",
            self.show(t)
        );
        (("raise".to_owned(), codes::E0502, message), help, fix)
    }

    /// E0311 at a raise of a value whose type would contain itself.
    fn cyclic_raise(&mut self, t: &Ty, at: TextRange) {
        let message = format!(
            "this raises a value of type `{}`, which would make that type contain itself",
            self.show(t)
        );
        self.error(codes::E0311, at, message);
    }

    /// A row variable's name, as a message writes it.
    fn row_param_name(&self, p: &RowParam) -> stilt_hir::hir::Name {
        match p {
            RowParam::Written(g) => (self.env.names)(g),
            RowParam::Passed { .. } => "_".into(),
        }
    }

    /// The key, code and message of a problem with a user-defined effect: one the row doesn't hold,
    /// E0512 if `unhandled` (handlers.no-effect-reaches-main) and E0502 otherwise
    /// (handlers.performing-operation), or one with other type arguments than the row's, E0311
    /// (handlers.effects-in-rows).
    fn effects(&self, problem: Problem, unhandled: bool) -> (String, Code, String) {
        match problem {
            Problem::MissingEffect(e) if unhandled => (
                format!("effect {}", e.name),
                codes::E0512,
                format!(
                    "this performs `{0}`, but no `with` around it handles `{0}`; wrap it in \
                     one: `with h {{ … }}`",
                    e.name
                ),
            ),
            Problem::MissingEffect(e) => (
                format!("effect {}", e.name),
                codes::E0502,
                format!("this performs `{}`, which the row doesn't declare", e.name),
            ),
            Problem::EffectMismatch(e, given, held) => {
                let frozen =
                    |ts: Vec<Ty>| ts.iter().map(|t| self.table.freeze(t)).collect::<Vec<_>>();
                let (given, held) = (frozen(given), frozen(held));
                (
                    format!("effect type {}", e.name),
                    codes::E0311,
                    format!(
                        "this performs `{}`, but the row holds `{}`",
                        self.show_effect(&e, &given),
                        self.show_effect(&e, &held)
                    ),
                )
            }
            _ => unreachable!("`report_in` gives only the problems of effects"),
        }
    }

    /// Fits the effects performed so far, in order, into a row (effects.missing-effects): the
    /// function's own if `own`. Each missing effect is reported where it first occurs, with
    /// what the row allows as its alternatives (goal admissible-alternatives).
    pub(super) fn settle(&mut self, effects: &[(Row, TextRange)], row: &Row, own: bool) {
        self.settle_handled(effects, row, (own, false), &Handled::Nothing);
    }

    /// [`State::settle`], handling `handled` on the way, with E0512 for a user-defined effect
    /// if `unhandled` (handlers.no-effect-reaches-main; tasks.sequential-run).
    pub(super) fn settle_handled(
        &mut self,
        effects: &[(Row, TextRange)],
        row: &Row,
        (own, unhandled): (bool, bool),
        handled: &Handled,
    ) {
        let mut reported = Reported::default();
        let first = self.errors.len();
        for (r, at) in effects {
            let problems = self.table.fit(handled, r, row);
            self.report_in(&mut reported, (*at, own, unhandled), problems);
        }
        let allows: Vec<Alternative> = self
            .table
            .row_elements(row, self.env.names)
            .into_iter()
            .map(|e| Alternative::new(AlternativeKind::Effect, e))
            .collect();
        for d in &mut self.errors[first..] {
            if d.code == codes::E0502 {
                *d = d.clone().with_alternatives(allows.iter().cloned());
            }
        }
    }
}
