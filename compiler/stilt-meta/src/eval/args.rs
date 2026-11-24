//! The arguments of a call (values.inout-arguments and values.left-to-right;
//! projections.when-projection-runs): evaluated from left to right, a spread's values in its place
//! (variadics.spread-expressions), and each `inout` one's place lent to the callee and written back
//! when the call ends, however it ends. A place rooted in a projection's call is prepared in its
//! turn, which evaluates the projection's arguments and its index expressions, and opened when the
//! call starts: the projection runs to its `yield`, the call runs on the yielded place, and the
//! projection resumes once the call ends.

use stilt_syntax::ast::Mode;
use stilt_types::tast::{Arg, Callee, Expr, ExprKind};
use stilt_types::ty::Ty;

use super::calls::Target;
use super::windows::Resolved;
use super::{Flow, Frame, Machine, R, substituted_all};
use crate::value::{Step, Value};

/// The evaluated arguments of a call.
pub(crate) struct Args<'a> {
    pub(crate) values: Vec<Value<'a>>,
    /// Each `inout` argument rooted in a variable, with its value's index.
    direct: Vec<(Resolved<'a>, usize)>,
    /// Each `inout` argument rooted in a projection's call, with its value's index.
    deferred: Vec<(Prepared<'a>, usize)>,
}

/// A projection's call, prepared: what it runs, its arguments, and the steps of the place from
/// the place it yields.
pub(crate) struct Prepared<'a> {
    target: Option<Target<'a>>,
    args: Args<'a>,
    steps: Vec<Step<'a>>,
}

impl<'a> Args<'a> {
    /// The place of each `inout` argument rooted in a variable, with its value's index.
    pub(crate) fn places(&self) -> &[(Resolved<'a>, usize)] {
        &self.direct
    }
}

impl<'a> Prepared<'a> {
    /// Its arguments, to be written back.
    pub(crate) fn into_args(self) -> Args<'a> {
        self.args
    }
}

/// Whether a place is rooted in a projection's call.
pub(crate) fn projected(place: &Expr) -> bool {
    match &place.kind {
        ExprKind::Project(..) => true,
        ExprKind::Field(base, _) | ExprKind::TupleField(base, _) | ExprKind::Index(base, _) => {
            projected(base)
        }
        _ => false,
    }
}

impl<'a> Machine<'a> {
    /// Evaluates a call's arguments.
    pub(crate) fn arguments(
        &mut self,
        fr: &mut Frame<'a>,
        args: &'a [Arg],
    ) -> Result<Args<'a>, Flow<'a>> {
        let mut out = Args {
            values: Vec::with_capacity(args.len()),
            direct: Vec::new(),
            deferred: Vec::new(),
        };
        for a in args {
            let at = out.values.len();
            match (&a.value.kind, a.mode) {
                (_, Mode::Inout) if projected(&a.value) => {
                    let prepared = self.prepare(fr, &a.value, Vec::new())?;
                    out.deferred.push((prepared, at));
                    out.values.push(Value::unit());
                }
                (_, Mode::Inout) => {
                    let place = self
                        .resolve(fr, &a.value)?
                        .expect("an `inout` argument is a place, as checking found");
                    out.values.push(Value::unit());
                    out.direct.push((place, at));
                }
                (ExprKind::Spread(_), _) => {
                    let spread = self.elements(fr, std::slice::from_ref(&a.value))?;
                    out.values.extend(spread);
                }
                _ => out.values.push(self.expr(fr, &a.value)?),
            }
        }
        // The places are read once every argument is evaluated, so that what the later ones
        // change reaches the callee (values.inout-arguments).
        for (place, i) in &out.direct {
            out.values[*i] = self.take_at(place)?;
        }
        Ok(out)
    }

    /// The value of a place, taken out of it until the call writes it back.
    fn take_at(&mut self, place: &Resolved<'a>) -> R<'a> {
        let mut out = Value::unit();
        self.at_place(place, &mut |_, v| {
            out = std::mem::replace(v, Value::unit());
            Ok(())
        })?;
        Ok(out)
    }

    /// Writes each `inout` argument rooted in a variable back into its place, and those of the
    /// projections prepared among the arguments.
    pub(crate) fn written_back(&mut self, args: Args<'a>) -> Result<(), Flow<'a>> {
        let Args {
            mut values,
            direct,
            deferred,
        } = args;
        for (prepared, _) in deferred {
            self.written_back(prepared.args)?;
        }
        for (place, i) in direct {
            let mut v = Some(std::mem::replace(&mut values[i], Value::unit()));
            self.at_place(&place, &mut |_, slot| {
                if let Some(x) = v.take() {
                    *slot = x;
                }
                Ok(())
            })?;
        }
        Ok(())
    }

    /// Prepares the place `place`, rooted in a projection's call, its steps from the yielded
    /// place being `steps` and then the ones above it.
    pub(crate) fn prepare(
        &mut self,
        fr: &mut Frame<'a>,
        place: &'a Expr,
        above: Vec<Step<'a>>,
    ) -> Result<Prepared<'a>, Flow<'a>> {
        let mut steps = above;
        let step = match &place.kind {
            ExprKind::Project(callee, targs, args, _) => {
                let mut prepared = self.prepare_call(fr, callee, targs, args)?;
                steps.reverse();
                prepared.steps = steps;
                return Ok(prepared);
            }
            ExprKind::Field(base, name) => (base, Step::Field(*name)),
            ExprKind::TupleField(base, i) => (base, Step::Elem(*i)),
            ExprKind::Index(base, key) => {
                let k = self.expr(fr, key)?;
                (base, Step::Key(k))
            }
            _ => unreachable!("a prepared place is rooted in a projection's call"),
        };
        steps.push(step.1);
        self.prepare(fr, step.0, steps)
    }

    /// Prepares a projection's call: its arguments, and what it runs.
    pub(crate) fn prepare_call(
        &mut self,
        fr: &mut Frame<'a>,
        callee: &'a Callee,
        targs: &'a [Ty],
        args: &'a [Arg],
    ) -> Result<Prepared<'a>, Flow<'a>> {
        let targs = substituted_all(fr, targs);
        let args = self.arguments(fr, args)?;
        let target = self.target(fr, callee, &targs, &args.values)?;
        Ok(Prepared {
            target: Some(target),
            args,
            steps: Vec::new(),
        })
    }

    /// Runs `inner` on the values of `args` with each prepared projection among them opened, in
    /// order, each on the place its steps reach from the place it yields, and held until
    /// `inner` ends.
    pub(crate) fn opened(
        &mut self,
        args: &mut Args<'a>,
        inner: &mut dyn FnMut(&mut Machine<'a>, &mut Vec<Value<'a>>) -> R<'a>,
    ) -> R<'a> {
        open(self, &mut args.deferred, &mut args.values, inner)
    }

    /// Opens a prepared projection's call for `visit`, on the place its steps reach.
    pub(crate) fn open_prepared(
        &mut self,
        prepared: &mut Prepared<'a>,
        visit: &mut super::places::Visit<'_, 'a>,
    ) -> Result<(), Flow<'a>> {
        let target = prepared
            .target
            .take()
            .expect("a prepared projection opens once");
        let steps = &prepared.steps;
        let mut target = Some(target);
        self.opened(&mut prepared.args, &mut |m, values| {
            let target = target.take().expect("the projection runs once");
            m.run_projection(target, values, &mut |m, yielded| {
                m.at_steps(yielded, steps, visit)
            })?;
            Ok(Value::unit())
        })
        .map(|_| ())
    }
}

/// Opens `deferred` in order, then runs `inner`: each projection's yielded place lends its
/// value, at its steps, to the argument it stands for while the rest runs.
fn open<'a>(
    m: &mut Machine<'a>,
    deferred: &mut [(Prepared<'a>, usize)],
    values: &mut Vec<Value<'a>>,
    inner: &mut dyn FnMut(&mut Machine<'a>, &mut Vec<Value<'a>>) -> R<'a>,
) -> R<'a> {
    let Some(((prepared, i), rest)) = deferred.split_first_mut() else {
        return inner(m, values);
    };
    let i = *i;
    let mut result: Option<R<'a>> = None;
    let opened = m.open_prepared(prepared, &mut |m, slot| {
        values[i] = std::mem::replace(slot, Value::unit());
        let r = open(m, rest, values, inner);
        *slot = std::mem::replace(&mut values[i], Value::unit());
        let failed = r.as_ref().err().cloned();
        result = Some(r);
        failed.map_or(Ok(()), Err)
    });
    match (opened, result) {
        (_, Some(Err(flow))) | (Err(flow), _) => Err(flow),
        (Ok(()), Some(Ok(v))) => Ok(v),
        (Ok(()), None) => unreachable!("a projection yields once on every path that returns"),
    }
}
