//! The values of a run that the advanced tier adds: handlers (handlers.handler-literals and
//! handlers.with), iterators (views.making-iterator, views.adapters, views.laziness and
//! views.consumers), lazy values (polymorphism.lazy-values) and the windows of writable views
//! (projections.writable-views and projections.places-through-views). A shared value
//! (shared.std-sync) is a [`Value::Shared`] of its own.

use std::sync::{Arc, Mutex};

use stilt_hir::hir::{Item, Name};

use super::Value;

/// A handler (handlers.handler-literals): its effect, whether it takes control (handlers.resuming),
/// and the closure of each of its operations.
#[derive(Debug)]
pub(crate) struct HandlerValue<'a> {
    pub(crate) effect: Item,
    pub(crate) control: bool,
    pub(crate) ops: Vec<(Name, Value<'a>)>,
}

/// An iterator: the description of its source and its adapters, which a consumer reads from
/// its start each time (views.laziness).
#[derive(Debug)]
pub(crate) enum IterValue<'a> {
    Elements(Vec<Value<'a>>),
    /// The integers from the first up to the last, without it.
    Range(i128, i128),
    Mapped(Arc<IterValue<'a>>, Value<'a>),
    Filtered(Arc<IterValue<'a>>, Value<'a>),
    Taken(Arc<IterValue<'a>>, i128),
    Skipped(Arc<IterValue<'a>>, i128),
    TakenWhile(Arc<IterValue<'a>>, Value<'a>),
    SkippedWhile(Arc<IterValue<'a>>, Value<'a>),
    Enumerated(Arc<IterValue<'a>>, i128),
    Zipped(Arc<IterValue<'a>>, Arc<IterValue<'a>>),
    Chained(Arc<IterValue<'a>>, Arc<IterValue<'a>>),
}

/// A lazy value (polymorphism.lazy-values): its function, and what it returned the first time any
/// copy of the value asked.
#[derive(Debug)]
pub(crate) struct Deferred<'a> {
    pub(crate) compute: Value<'a>,
    pub(crate) result: Mutex<Option<Value<'a>>>,
}

/// A part of a place: a field, a tuple's element, or a key of a list or a map.
#[derive(Clone, Debug)]
pub(crate) enum Step<'a> {
    Field(Name),
    Elem(usize),
    Key(Value<'a>),
}

/// A window into the part `start..stop` of the list that the place `root` and `path` of a frame's
/// locals holds: a writable view, whose writes write the place (projections.places-through-views).
#[derive(Debug)]
pub(crate) struct Window<'a> {
    pub(crate) locals: crate::eval::Locals<'a>,
    pub(crate) root: usize,
    pub(crate) path: Vec<Step<'a>>,
    pub(crate) start: usize,
    pub(crate) stop: usize,
}
