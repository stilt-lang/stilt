//! Writable views (projections.writable-views, projections.what-view-writes and
//! projections.places-through-views): windows into the part of a list that a place of a frame
//! holds. A write through a window writes the place, so a window can't be told from the part it
//! views while the law of exclusivity keeps every other access away (projections.what-view-writes);
//! a read of a window reads the part. A place rooted in a projection's call is the yielded place's
//! value for as long as the access runs, which a window views through a temporary place of its own.

use std::sync::{Arc, LazyLock, RwLock};

use stilt_hir::hir::Name;
use stilt_types::tast::{Arg, Callee, Expr, ExprKind};

use super::{Flow, Frame, Locals, Machine, R, panic};
use crate::frame::lock;
use crate::value::{Step, Value, Window};

/// The natives of `std.view` that take the place of a list or a view `inout` and give a window
/// into it (projections.writable-views).
#[derive(Clone, Copy, Debug)]
pub(crate) enum WindowNative {
    Into,
    Part,
    Split,
}

/// Which of them `callee` is, if it is one.
pub(crate) fn window_native(callee: &Callee) -> Option<WindowNative> {
    static VIEW: LazyLock<Name> = LazyLock::new(|| Name::from("std.view"));
    let Callee::Function(item) = callee else {
        return None;
    };
    if item.home != *VIEW {
        return None;
    }
    match &*item.name {
        "into" => Some(WindowNative::Into),
        "part" => Some(WindowNative::Part),
        "split" => Some(WindowNative::Split),
        _ => None,
    }
}

/// A place of a frame's locals: its root's slot and its steps.
#[derive(Clone, Debug)]
pub(crate) struct Resolved<'a> {
    pub(crate) locals: Locals<'a>,
    pub(crate) root: usize,
    pub(crate) path: Vec<Step<'a>>,
}

/// The bounds `start..stop` of a part of a list of `length` elements, which panic as `View.of`
/// does (views.making-view).
fn bounds<'a>(length: usize, start: i128, stop: i128) -> Result<(usize, usize), Flow<'a>> {
    let fits = 0 <= start && start <= stop && usize::try_from(stop).is_ok_and(|s| s <= length);
    if !fits {
        return panic(
            "bounds",
            format!("the range {start}..{stop} is out of bounds for a list of length {length}"),
        );
    }
    Ok((
        usize::try_from(start).unwrap_or(0),
        usize::try_from(stop).unwrap_or(0),
    ))
}

impl<'a> Machine<'a> {
    /// The place that `place` names, its index expressions evaluated from the left, if it is
    /// rooted in a local.
    pub(crate) fn resolve(
        &mut self,
        fr: &mut Frame<'a>,
        place: &'a Expr,
    ) -> Result<Option<Resolved<'a>>, Flow<'a>> {
        let base = match &place.kind {
            ExprKind::Local(id) => {
                return Ok(Some(Resolved {
                    locals: Arc::clone(&fr.locals),
                    root: fr.slot(*id),
                    path: Vec::new(),
                }));
            }
            ExprKind::Field(base, _) | ExprKind::TupleField(base, _) | ExprKind::Index(base, _) => {
                base
            }
            _ => return Ok(None),
        };
        let Some(mut resolved) = self.resolve(fr, base)? else {
            return Ok(None);
        };
        let step = match &place.kind {
            ExprKind::Field(_, name) => Step::Field(*name),
            ExprKind::TupleField(_, i) => Step::Elem(*i),
            ExprKind::Index(_, key) => Step::Key(self.expr(fr, key)?),
            _ => unreachable!("a resolved place's step is a field, an element or an index"),
        };
        resolved.path.push(step);
        Ok(Some(resolved))
    }

    /// Applies `visit` to the value at a resolved place.
    pub(crate) fn at_place(
        &mut self,
        place: &Resolved<'a>,
        visit: &mut super::places::Visit<'_, 'a>,
    ) -> Result<(), Flow<'a>> {
        let mut root = lock(&place.locals)
            .get_mut(place.root)
            .and_then(Option::take)
            .unwrap_or_else(Value::unit);
        let result = self.at_steps(&mut root, &place.path, visit);
        let mut locals = lock(&place.locals);
        if place.root >= locals.len() {
            locals.resize(place.root + 1, None);
        }
        locals[place.root] = Some(root);
        result
    }

    /// The value at a resolved place.
    pub(crate) fn read_place(&mut self, place: &Resolved<'a>) -> R<'a> {
        let mut out = Value::unit();
        self.at_place(place, &mut |_, v| {
            out = v.clone();
            Ok(())
        })?;
        Ok(out)
    }

    /// The place of a window's element `i`, counted from its start, which panics past its end.
    fn window_element(w: &Window<'a>, key: &Value<'a>) -> Result<Resolved<'a>, Flow<'a>> {
        let i = key.as_int();
        let length = w.stop - w.start;
        let Some(i) = usize::try_from(i).ok().filter(|&i| i < length) else {
            return panic(
                "bounds",
                format!("index {i} is out of bounds for a view of length {length}"),
            );
        };
        let mut path = w.path.clone();
        path.push(Step::Key(Value::i64(
            i128::try_from(w.start + i).unwrap_or(0),
        )));
        Ok(Resolved {
            locals: Arc::clone(&w.locals),
            root: w.root,
            path,
        })
    }

    /// Applies `visit` to element `key` of the part a window views, in the place it views.
    pub(crate) fn window_at(
        &mut self,
        w: &Window<'a>,
        key: &Value<'a>,
        visit: &mut super::places::Visit<'_, 'a>,
    ) -> Result<(), Flow<'a>> {
        let place = Self::window_element(w, key)?;
        self.at_place(&place, visit)
    }

    /// Element `key` of the part a window views.
    pub(crate) fn window_read(&mut self, w: &Window<'a>, key: &Value<'a>) -> R<'a> {
        let place = Self::window_element(w, key)?;
        self.read_place(&place)
    }

    /// The part a window views, as a value of its own: what a read of the window reads (rule
    /// 11), and every other value as it is.
    pub(crate) fn thaw(&mut self, v: Value<'a>) -> R<'a> {
        let Value::Window(w) = v else {
            return Ok(v);
        };
        let place = Resolved {
            locals: Arc::clone(&w.locals),
            root: w.root,
            path: w.path.clone(),
        };
        let held = self.read_place(&place)?;
        let whole = self.thaw(held)?;
        Ok(Value::list(
            whole
                .as_list()
                .get(w.start..w.stop)
                .unwrap_or_default()
                .to_vec(),
        ))
    }

    /// A call of `into`, `part` or `split` (projections.writable-views): its arguments, the place
    /// first, then the window or windows into that place.
    pub(super) fn window_call(
        &mut self,
        fr: &mut Frame<'a>,
        which: WindowNative,
        args: &'a [Arg],
    ) -> R<'a> {
        self.run.step()?;
        let place = &args[0].value;
        let resolved = self.resolve(fr, place)?;
        let mut rest = Vec::with_capacity(2);
        for a in &args[1..] {
            rest.push(self.expr(fr, &a.value)?);
        }
        match resolved {
            Some(at) => self.windows(which, &at, &rest),
            None => self.window_of_projection(fr, which, place, rest),
        }
    }

    /// The windows of a call into a place rooted in a projection's call: windows into a
    /// temporary place that holds the yielded place's value while the access runs, and gives
    /// it back when the access ends.
    fn window_of_projection(
        &mut self,
        fr: &mut Frame<'a>,
        which: WindowNative,
        place: &'a Expr,
        rest: Vec<Value<'a>>,
    ) -> R<'a> {
        let mut rest = Some(rest);
        let mut out = Value::unit();
        self.with_place(fr, place, &mut |m, slot| {
            let temporary: Locals<'a> = Arc::new(RwLock::new(vec![Some(std::mem::replace(
                slot,
                Value::unit(),
            ))]));
            let at = Resolved {
                locals: Arc::clone(&temporary),
                root: 0,
                path: Vec::new(),
            };
            let result = m.windows(which, &at, &rest.take().unwrap_or_default());
            *slot = lock(&temporary)[0].clone().unwrap_or_else(Value::unit);
            out = result?;
            Ok(())
        })?;
        Ok(out)
    }

    /// The window that `into` or `part` gives, or the call of `split`'s closure on its two.
    fn windows(&mut self, which: WindowNative, at: &Resolved<'a>, rest: &[Value<'a>]) -> R<'a> {
        let held = self.read_place(at)?;
        let int = |i: usize| rest.get(i).map_or(0, Value::as_int);
        match (which, held) {
            (WindowNative::Part, Value::Window(w)) => {
                let (start, stop) = bounds(w.stop - w.start, int(0), int(1))?;
                Ok(Value::Window(Arc::new(Window {
                    locals: Arc::clone(&w.locals),
                    root: w.root,
                    path: w.path.clone(),
                    start: w.start + start,
                    stop: w.start + stop,
                })))
            }
            (WindowNative::Into | WindowNative::Part, list) => {
                let (start, stop) = bounds(list.as_list().len(), int(0), int(1))?;
                Ok(window(at, start, stop))
            }
            (WindowNative::Split, list) => {
                let length = list.as_list().len();
                let (split, _) = bounds(length, int(0), int(0))?;
                let f = rest.get(1).cloned().unwrap_or_else(Value::unit);
                let mut halves = vec![window(at, 0, split), window(at, split, length)];
                self.apply_value(&f, &mut halves)?;
                Ok(Value::unit())
            }
        }
    }

    /// The value a body returned, its windows into the `inout` parameters of the frame whose locals
    /// are `callee` writing the arguments' places instead (projections.what-view-writes):
    /// `params` gives each parameter's slot with its argument's place.
    pub(crate) fn retargeted(
        v: Value<'a>,
        callee: &Locals<'a>,
        params: &[(usize, Resolved<'a>)],
    ) -> Value<'a> {
        match v {
            Value::Window(w) if Arc::ptr_eq(&w.locals, callee) => {
                match params.iter().find(|(slot, _)| *slot == w.root) {
                    Some((_, place)) => {
                        let mut path = place.path.clone();
                        path.extend(w.path.iter().cloned());
                        Value::Window(Arc::new(Window {
                            locals: Arc::clone(&place.locals),
                            root: place.root,
                            path,
                            start: w.start,
                            stop: w.stop,
                        }))
                    }
                    None => Value::Window(w),
                }
            }
            Value::Variant(x) if &*x.0.name == "Some" && x.1.len() == 1 => {
                let inner = Self::retargeted(x.1[0].clone(), callee, params);
                Value::variant(x.0.clone(), vec![inner])
            }
            v => v,
        }
    }
}

/// A window into `start..stop` of the list at a place.
fn window<'a>(at: &Resolved<'a>, start: usize, stop: usize) -> Value<'a> {
    Value::Window(Arc::new(Window {
        locals: Arc::clone(&at.locals),
        root: at.root,
        path: at.path.clone(),
        start,
        stop,
    }))
}

/// Whether a value a body returns holds a window into the locals `callee`.
pub(crate) fn holds_window_into<'a>(v: &Value<'a>, callee: &Locals<'a>) -> bool {
    match v {
        Value::Window(w) => Arc::ptr_eq(&w.locals, callee),
        Value::Variant(x) if &*x.0.name == "Some" => {
            x.1.first().is_some_and(|v| holds_window_into(v, callee))
        }
        _ => false,
    }
}
