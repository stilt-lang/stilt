//! Projections (projections.yield, projections.when-projection-runs and
//! projections.raising-during-access): a projection's body runs on a fiber to its `yield`, which
//! hands the value of its place to the caller's access; the body resumes with the value the access
//! leaves, once the access ends, and doesn't resume when the access raises or panics, its `inout`
//! arguments then holding what it changed before the `yield`.

use std::sync::Mutex;
use std::sync::mpsc::channel;

use stilt_types::tast::Expr;

use super::calls::Target;
use super::places::Visit;
use super::{Flow, Frame, Machine, R};
use crate::fiber::{Down, Up, receive, send};
use crate::value::{Step, Value};

impl<'a> Machine<'a> {
    /// Runs a projection on `values`, its body's `yield` handing its place to `visit`, and
    /// leaves the final values of its `inout` parameters in `values`.
    pub(crate) fn run_projection(
        &mut self,
        target: Target<'a>,
        values: &mut Vec<Value<'a>>,
        visit: &mut Visit<'_, 'a>,
    ) -> Result<(), Flow<'a>> {
        crate::eval::reserve(crate::fiber::FIBER)?;
        let (done, waits) = channel();
        let waits = Mutex::new(waits);
        let outer = self.fx.yield_to.replace(done.clone());
        let mut given = std::mem::take(values);
        let (result, finals) = self.on_fiber(
            done,
            move |m| {
                let r = m.apply(target, &mut given);
                Up::Done(r, given)
            },
            |m| m.serve(&waits, outer.as_ref(), visit),
        );
        *values = finals;
        result
    }

    /// Serves a projection's `yield`, and gives how it ended: the access's error, if the access
    /// raised or panicked, and otherwise the body's.
    fn serve(
        &mut self,
        waits: &Mutex<std::sync::mpsc::Receiver<crate::fiber::Message<'a>>>,
        outer: Option<&std::sync::mpsc::Sender<crate::fiber::Message<'a>>>,
        visit: &mut Visit<'_, 'a>,
    ) -> (Result<(), Flow<'a>>, Vec<Value<'a>>) {
        let mut accessed: Option<Result<(), Flow<'a>>> = None;
        loop {
            let (up, baton) = receive(waits);
            self.take_back(baton);
            let mine = std::mem::replace(&mut self.fx.yield_to, outer.cloned());
            match up {
                Up::Yielded { mut value, reply } => {
                    let r = visit(self, &mut value);
                    self.fx.yield_to = mine;
                    let down = if r.is_ok() {
                        Down::Resume(value)
                    } else {
                        Down::Abandon(Some(value))
                    };
                    accessed = Some(r);
                    send(&reply, (down, self.hand()));
                }
                Up::Done(r, finals) => {
                    let result = match accessed {
                        Some(Err(flow)) => Err(flow),
                        Some(Ok(())) => r.map(|_| ()),
                        None => match r {
                            Err(flow) => Err(flow),
                            Ok(_) => unreachable!("a projection that returns has yielded"),
                        },
                    };
                    return (result, finals);
                }
                Up::Perform { .. } => unreachable!("a performance goes to its handler's `with`"),
            }
        }
    }

    /// `yield place`: hands the place's value to the caller's access, and takes the value it
    /// leaves (projections.yield).
    pub(super) fn yield_place(
        &mut self,
        fr: &mut Frame<'a>,
        place: &'a Expr,
    ) -> Result<(), Flow<'a>> {
        self.with_place(fr, place, &mut |m, v| m.hand_up(v))
    }

    fn hand_up(&mut self, v: &mut Value<'a>) -> Result<(), Flow<'a>> {
        let to = self
            .fx
            .yield_to
            .clone()
            .expect("a `yield` runs in a projection's body");
        let (reply, answer) = channel();
        let value = std::mem::replace(v, Value::unit());
        send(&to, (Up::Yielded { value, reply }, self.hand()));
        drop(to);
        match self.wait_reply(&answer) {
            Down::Resume(x) => {
                *v = x;
                Ok(())
            }
            Down::Abandon(x) => {
                if let Some(x) = x {
                    *v = x;
                }
                Err(Flow::Abandon)
            }
        }
    }

    /// A read of a projection's call, which copies the yielded place's value out
    /// (projections.call-is-place).
    pub(super) fn project_read(&mut self, fr: &mut Frame<'a>, e: &'a Expr) -> R<'a> {
        let mut out = Value::unit();
        self.with_place(fr, e, &mut |_, v| {
            out = v.clone();
            Ok(())
        })?;
        Ok(out)
    }

    /// Applies `visit` to the part of `v` that `steps` reach.
    pub(crate) fn at_steps(
        &mut self,
        v: &mut Value<'a>,
        steps: &[Step<'a>],
        visit: &mut Visit<'_, 'a>,
    ) -> Result<(), Flow<'a>> {
        let Some((first, rest)) = steps.split_first() else {
            return visit(self, v);
        };
        match first {
            Step::Field(name) => match v {
                Value::Record(r) => match std::sync::Arc::make_mut(r)
                    .1
                    .slots()
                    .iter_mut()
                    .find(|(n, _)| n == name)
                {
                    Some((_, slot)) => self.at_steps(slot, rest, visit),
                    None => Ok(()),
                },
                _ => Ok(()),
            },
            Step::Elem(i) => match v {
                Value::Tuple(xs) => match std::sync::Arc::make_mut(xs).slots().get_mut(*i) {
                    Some(slot) => self.at_steps(slot, rest, visit),
                    None => Ok(()),
                },
                _ => Ok(()),
            },
            Step::Key(k) => self.element(v, k, &mut |m, slot| m.at_steps(slot, rest, visit)),
        }
    }
}
