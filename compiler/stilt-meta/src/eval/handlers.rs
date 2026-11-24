//! Handlers (handlers.handler-literals and handlers.resuming), deep and one-shot, as the reference
//! interpreter runs them. The handlers installed form a stack, innermost first, that a performance
//! searches for its effect. A handler that resumes at once is called where the operation is
//! performed, with the stack outside its `with`, so that its body performs its own effect outside
//! it; one that takes control runs its `with`'s block on a fiber, whose performances wait for the
//! body to resume them, which it does at most once, or to drop the rest of the block.

use std::sync::atomic::Ordering;
use std::sync::mpsc::channel;
use std::sync::{Arc, Mutex};

use stilt_hir::hir::{Item, Name};
use stilt_types::tast::{Block, Expr, HandlerExpr};

use super::{Flow, Frame, Machine, R};
use crate::fiber::{Controlled, Down, Installed, Resumption, Up, nearest, push, receive, send};
use crate::value::{HandlerValue, Value};

/// A handler of `async` installs nothing: every task runs to its end where it starts
/// (tasks.sequential-run).
fn is_async(effect: &Item) -> bool {
    &*effect.home == "std.prelude" && &*effect.name == "async"
}

/// The closure that implements `name` (handlers.handler-literals), which every handler has for each
/// operation of its effect.
fn operation<'a>(h: &HandlerValue<'a>, name: Name) -> Value<'a> {
    h.ops
        .iter()
        .find(|(n, _)| *n == name)
        .map(|(_, f)| f.clone())
        .expect("a handler implements each operation of its effect")
}

impl<'a> Machine<'a> {
    /// A handler literal's value: its operations' closures, made in the frame
    /// (handlers.handler-literals).
    pub(super) fn handler_literal(&mut self, fr: &mut Frame<'a>, h: &'a HandlerExpr) -> R<'a> {
        let mut ops = Vec::with_capacity(h.ops.len());
        for (name, e) in &h.ops {
            ops.push((*name, self.expr(fr, e)?));
        }
        Ok(Value::Handler(Arc::new(HandlerValue {
            effect: h.effect.clone(),
            control: h.control,
            ops,
        })))
    }

    /// `with h { block }` (handlers.with): the block with the handler installed innermost, and the
    /// stack as it was once the block ends, however it ends.
    pub(super) fn with(&mut self, fr: &mut Frame<'a>, h: &'a Expr, block: &'a Block) -> R<'a> {
        let Value::Handler(handler) = self.expr(fr, h)? else {
            unreachable!("a `with` installs a handler, as its checking found")
        };
        if is_async(&handler.effect) {
            return self.block(fr, block);
        }
        let outside = self.fx.stack.clone();
        let resumes = self.fx.resumes.clone();
        let result = if handler.control {
            self.controlled(fr, handler, block)
        } else {
            let entry = Installed {
                handler,
                outside: outside.clone(),
                with: None,
            };
            self.fx.stack = Some(push(entry, outside.clone()));
            self.block(fr, block)
        };
        self.fx.stack = outside;
        self.fx.resumes = resumes;
        result
    }

    /// The block of a `with` whose handler takes control, on a fiber, while the handler's
    /// bodies run here on its performances.
    fn controlled(
        &mut self,
        fr: &mut Frame<'a>,
        handler: Arc<HandlerValue<'a>>,
        block: &'a Block,
    ) -> R<'a> {
        crate::eval::reserve(crate::fiber::FIBER)?;
        let (to_with, waits) = channel();
        let outside = self.fx.stack.clone();
        let with = Controlled {
            handler: Arc::clone(&handler),
            outside: outside.clone(),
            waits: Arc::new(Mutex::new(waits)),
        };
        let entry = Installed {
            handler,
            outside: outside.clone(),
            with: Some(to_with.clone()),
        };
        self.fx.stack = Some(push(entry, outside));
        self.on_fiber(
            to_with,
            move |m| Up::Done(m.block(fr, block), Vec::new()),
            |m| m.drive(&with),
        )
    }

    /// Waits for the block of `with` to end, or to perform an operation of its handler, whose
    /// body then gives the value.
    fn drive(&mut self, with: &Controlled<'a>) -> R<'a> {
        let (up, baton) = receive(&with.waits);
        self.take_back(baton);
        match up {
            Up::Done(result, _) => result,
            Up::Perform { name, args, reply } => self.take_control(with, name, args, reply),
            Up::Yielded { .. } => unreachable!("a `yield` goes to its projection's caller"),
        }
    }

    /// handlers.resuming: the body of the operation `name` on `args`, run with the handlers outside
    /// its `with`. A body that never resumes drops the rest of the block, which ends before the
    /// body's value is the `with`'s.
    fn take_control(
        &mut self,
        with: &Controlled<'a>,
        name: Name,
        mut args: Vec<Value<'a>>,
        reply: std::sync::mpsc::Sender<crate::fiber::Reply<'a>>,
    ) -> R<'a> {
        let site_resumes = self.fx.resumes.clone();
        let resumption = Arc::new(Resumption {
            reply,
            site: self.fx.stack.clone(),
            site_resumes: site_resumes.clone(),
            with: with.clone(),
            resumed: std::sync::atomic::AtomicBool::new(false),
        });
        self.fx.stack.clone_from(&with.outside);
        self.fx.resumes = site_resumes;
        self.fx.resumes.push(Arc::clone(&resumption));
        let op = operation(&with.handler, name);
        let result = self.apply_value(&op, &mut args);
        if !resumption.resumed.load(Ordering::Relaxed) {
            self.drop_block(&resumption);
        }
        result
    }

    /// Tells the performance that waits for `r` to leave, and waits for the block's fiber to
    /// end, which it does once the rest of the block has unwound.
    fn drop_block(&mut self, r: &Resumption<'a>) {
        send(&r.reply, (Down::Abandon(None), self.hand()));
        loop {
            let (up, baton) = receive(&r.with.waits);
            self.take_back(baton);
            match up {
                Up::Done(..) => return,
                Up::Perform { reply, .. } | Up::Yielded { reply, .. } => {
                    send(&reply, (Down::Abandon(None), self.hand()));
                }
            }
        }
    }

    /// `resume(v)` in the body of the operation that runs: the rest of its `with`'s block from
    /// the performance, with the handlers and the `resume`s it had there, and what the block
    /// ends with (handlers.resuming).
    pub(super) fn resume(&mut self, v: Value<'a>) -> R<'a> {
        let r = Arc::clone(
            self.fx
                .resumes
                .last()
                .expect("a `resume` is in the body of an operation that took control"),
        );
        r.resumed.store(true, Ordering::Relaxed);
        let mine = std::mem::replace(&mut self.fx.resumes, r.site_resumes.clone());
        self.fx.stack = r.site.clone();
        send(&r.reply, (Down::Resume(v), self.hand()));
        let result = self.drive(&r.with);
        self.fx.stack = r.with.outside.clone();
        self.fx.resumes = mine;
        result
    }

    /// handlers.performing-operation: a performance of `name` of `effect` on the nearest handler of
    /// its effect.
    pub(super) fn perform(&mut self, effect: &Item, name: Name, mut args: Vec<Value<'a>>) -> R<'a> {
        let entry = nearest(&self.fx.stack, effect)
            .expect("every performance runs under a handler of its effect (handlers.no-effect-reaches-main)");
        match &entry.with {
            None => {
                let site = std::mem::replace(&mut self.fx.stack, entry.outside.clone());
                let op = operation(&entry.handler, name);
                let result = self.apply_value(&op, &mut args);
                self.fx.stack = site;
                result
            }
            Some(with) => {
                let with = with.clone();
                let (reply, answer) = channel();
                drop(entry);
                send(&with, (Up::Perform { name, args, reply }, self.hand()));
                drop(with);
                match self.wait_reply(&answer) {
                    Down::Resume(v) => Ok(v),
                    Down::Abandon(_) => Err(Flow::Abandon),
                }
            }
        }
    }
}
