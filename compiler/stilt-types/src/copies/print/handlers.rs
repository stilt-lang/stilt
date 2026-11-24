//! The print of the forms of effects and handlers (handlers.handler-literals, handlers.with and
//! handlers.resuming), and of `when` (shared.when).

use std::fmt::Write as _;

use super::Printer;
use crate::tast::{Expr, ExprKind};

impl Printer<'_> {
    /// A handler literal, a `with` and a `resume` (handlers.handler-literals, handlers.with and
    /// handlers.resuming).
    pub(super) fn handling(&mut self, e: &Expr) {
        match &e.kind {
            ExprKind::Handler(h) => {
                let _ = write!(self.out, "handler{} ", h.control);
                self.item(&h.effect);
                for (name, op) in &h.ops {
                    self.text(name);
                    self.expr(op);
                }
            }
            ExprKind::With(handler, effect, args, block) => {
                self.tag("with");
                self.expr(handler);
                self.item(effect);
                self.tys(args);
                self.block(block);
            }
            ExprKind::Resume(value) => {
                self.tag("resume");
                if let Some(v) = value {
                    self.expr(v);
                }
            }
            // shared.when
            ExprKind::When(held, block) => {
                self.tag("when");
                for (h, place) in held {
                    self.expr(h);
                    self.local(*place);
                }
                self.block(block);
            }
            // macros.quote: a quote is its text and its splices.
            ExprKind::Quote(q) => {
                self.tag("quote");
                self.text(&q.written);
                for s in &q.splices {
                    self.expr(&s.value);
                }
            }
            _ => self.tag("!"),
        }
    }
}
