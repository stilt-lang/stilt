//! Fibers: parts of a run that wait while other code runs, each on a thread of its own, which
//! the run's state passes between so that one runs at a time. The block of a `with` whose
//! handler takes control runs on one, so that a performance can wait for the handler's body to
//! resume it (handlers.resuming), and so does the body of a projection, which waits at its `yield`
//! while its caller's access runs (projections.yield and projections.when-projection-runs). The
//! run's state, its counts among it, moves with each message, so that the run counts as one
//! (macros.step-limits).

use std::collections::HashMap;
use std::sync::atomic::AtomicBool;
use std::sync::mpsc::{Receiver, Sender};
use std::sync::{Arc, Mutex, PoisonError};

use stilt_hir::hir::{Item, Name};

use crate::eval::{Machine, R};
use crate::limits::Run;
use crate::run::Io;
use crate::value::{HandlerValue, Value};

/// The stack of a fiber's thread: enough for 10,000 frames of the deepest code, as the run's.
const STACK: usize = 1 << 30;

/// What a fiber weighs in the run's memory while it lives, for its thread (macros.step-limits),
/// so that a run nests at most a few hundred, and a run that would nest more stops as one out of
/// memory does, before the system refuses it a thread.
pub(crate) const FIBER: usize = 1 << 20;

/// A handler installed by a `with` (handlers.with): with the stack outside it, where its
/// bodies run, and, for one that takes control, where its `with` waits for performances.
#[derive(Debug)]
pub(crate) struct Installed<'a> {
    pub(crate) handler: Arc<HandlerValue<'a>>,
    pub(crate) outside: Stack<'a>,
    pub(crate) with: Option<Sender<Message<'a>>>,
}

/// The handlers installed, innermost first.
pub(crate) type Stack<'a> = Option<Arc<Node<'a>>>;

#[derive(Debug)]
pub(crate) struct Node<'a> {
    pub(crate) entry: Arc<Installed<'a>>,
    pub(crate) next: Stack<'a>,
}

/// The stack with `entry` installed innermost.
pub(crate) fn push<'a>(entry: Installed<'a>, next: Stack<'a>) -> Arc<Node<'a>> {
    Arc::new(Node {
        entry: Arc::new(entry),
        next,
    })
}

/// The nearest handler of `effect`.
pub(crate) fn nearest<'a>(stack: &Stack<'a>, effect: &Item) -> Option<Arc<Installed<'a>>> {
    let mut at = stack.as_ref();
    while let Some(node) = at {
        if node.entry.handler.effect == *effect {
            return Some(Arc::clone(&node.entry));
        }
        at = node.next.as_ref();
    }
    None
}

/// A handler that takes control, as the `with` that installed it drives it.
#[derive(Clone, Debug)]
pub(crate) struct Controlled<'a> {
    pub(crate) handler: Arc<HandlerValue<'a>>,
    pub(crate) outside: Stack<'a>,
    pub(crate) waits: Arc<Mutex<Receiver<Message<'a>>>>,
}

/// The `resume` of the body of an operation that took control: the performance that waits for
/// it, the handlers and the `resume`s it had there, and the `with` that drives it.
#[derive(Debug)]
pub(crate) struct Resumption<'a> {
    pub(crate) reply: Sender<Reply<'a>>,
    pub(crate) site: Stack<'a>,
    pub(crate) site_resumes: Vec<Arc<Resumption<'a>>>,
    pub(crate) with: Controlled<'a>,
    pub(crate) resumed: AtomicBool,
}

/// What the running code is in: the handlers installed, the `resume`s of the bodies that run,
/// innermost last, the values that the `when`s around it hold (shared.when), and the channel
/// of the projection whose body runs, which a `yield` hands its place to.
#[derive(Debug, Default)]
pub(crate) struct Effects<'a> {
    pub(crate) stack: Stack<'a>,
    pub(crate) resumes: Vec<Arc<Resumption<'a>>>,
    pub(crate) held: Vec<Arc<Mutex<Value<'a>>>>,
    pub(crate) yield_to: Option<Sender<Message<'a>>>,
}

/// What a fiber, or a performance under a `with`, tells the thread that waits for it.
#[derive(Debug)]
pub(crate) enum Up<'a> {
    /// A performance of an operation of a handler that takes control, on its arguments.
    Perform {
        name: Name,
        args: Vec<Value<'a>>,
        reply: Sender<Reply<'a>>,
    },
    /// A projection's `yield`, with the value of the place it yields.
    Yielded {
        value: Value<'a>,
        reply: Sender<Reply<'a>>,
    },
    /// The fiber's end, with its result and the final values of the arguments it was given.
    Done(R<'a>, Vec<Value<'a>>),
}

/// What a performance or a `yield` is told: to go on with a value, or to leave, with the value
/// its place holds then.
#[derive(Debug)]
pub(crate) enum Down<'a> {
    Resume(Value<'a>),
    Abandon(Option<Value<'a>>),
}

pub(crate) type Message<'a> = (Up<'a>, Baton<'a>);
pub(crate) type Reply<'a> = (Down<'a>, Baton<'a>);

/// The state of a run, which the thread that runs holds.
#[derive(Debug)]
pub(crate) struct Baton<'a> {
    run: Run,
    io: Io<'a>,
    constants: HashMap<(Item, Option<Name>), Value<'a>>,
    fx: Effects<'a>,
}

/// The next message on `waits`. A fiber always sends one before it ends, so a channel that
/// closes first is a bug of the interpreter.
pub(crate) fn receive<'a>(waits: &Mutex<Receiver<Message<'a>>>) -> Message<'a> {
    waits
        .lock()
        .unwrap_or_else(PoisonError::into_inner)
        .recv()
        .expect("a fiber of the run ended without saying so")
}

/// Sends a message, which the thread it goes to always waits for.
pub(crate) fn send<T>(to: &Sender<T>, message: T) {
    to.send(message)
        .expect("a fiber of the run waits for each message sent to it");
}

impl<'a> Machine<'a> {
    /// The run's state, given to another thread, this one keeping nothing of it.
    pub(crate) fn hand(&mut self) -> Baton<'a> {
        let home = self.run.home;
        Baton {
            run: std::mem::replace(&mut self.run, Run::new(home)),
            io: self.io.take(),
            constants: std::mem::take(&mut self.constants),
            fx: std::mem::take(&mut self.fx),
        }
    }

    /// Takes the run's state back from the thread that held it.
    pub(crate) fn take_back(&mut self, baton: Baton<'a>) {
        self.run = baton.run;
        self.io = baton.io;
        self.constants = baton.constants;
        self.fx = baton.fx;
    }

    /// Runs `work` on a fiber, which ends by sending `done` what it gives, while `drive` runs
    /// here and waits for the fiber's messages; both end before this does.
    pub(crate) fn on_fiber<T>(
        &mut self,
        done: Sender<Message<'a>>,
        work: impl FnOnce(&mut Machine<'a>) -> Up<'a> + Send,
        drive: impl FnOnce(&mut Machine<'a>) -> T,
    ) -> T {
        let image = self.image;
        let baton = self.hand();
        let meter = crate::value::meter();
        let _thread = crate::value::Held::new(FIBER);
        std::thread::scope(|s| {
            std::thread::Builder::new()
                .name("macro fiber".to_owned())
                .stack_size(STACK)
                .spawn_scoped(s, move || {
                    if let Some(meter) = &meter {
                        crate::value::use_meter(meter);
                    }
                    let mut m = Machine::from_baton(image, baton);
                    let up = work(&mut m);
                    send(&done, (up, m.hand()));
                })
                .expect("a thread for a fiber of the run");
            drive(self)
        })
    }

    fn from_baton(image: &'a crate::image::Image<'a>, baton: Baton<'a>) -> Self {
        Machine {
            image,
            run: baton.run,
            io: baton.io,
            constants: baton.constants,
            fx: baton.fx,
            escaped: None,
            pool: crate::frame::Pool::default(),
        }
    }

    /// Waits for what `reply` is told, and takes the run back with it.
    pub(crate) fn wait_reply(&mut self, reply: &Receiver<Reply<'a>>) -> Down<'a> {
        let (down, baton) = reply
            .recv()
            .expect("a performance or a yield is always answered");
        self.take_back(baton);
        down
    }
}
