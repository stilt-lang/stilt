//! The memory of a macro's run (macros.step-limits): every value that a run makes on the heap,
//! a text, a list, a map, a tuple, a record, a variant, a closure or code, is weighed as it is
//! made and dropped, so that the run stops once they would hold more than [`MEMORY`] bytes.
//! Each weighs what it holds and a share for its allocation, so that many small values weigh
//! about what they take.

use std::cell::RefCell;
use std::ops::Deref;
use std::sync::Arc;
use std::sync::atomic::{AtomicUsize, Ordering};

/// The most bytes that the values of a run may hold (macros.step-limits).
pub(crate) const MEMORY: usize = 512 << 20;

/// What an allocation takes beside what it holds: the counts of the `Arc` that holds the value,
/// and the value's own head.
const OVERHEAD: usize = 2 * std::mem::size_of::<usize>() + std::mem::size_of::<Counted<()>>();

/// The bytes that the values of one run hold, which every thread of the run weighs its values
/// on.
pub(crate) type Meter = Arc<AtomicUsize>;

thread_local! {
    static METER: RefCell<Option<Meter>> = const { RefCell::new(None) };
}

/// Makes `meter` the one that the values this thread makes are weighed on.
pub(crate) fn use_meter(meter: &Meter) {
    METER.with(|m| *m.borrow_mut() = Some(Arc::clone(meter)));
}

/// The meter of this thread's run.
pub(crate) fn meter() -> Option<Meter> {
    METER.with(|m| m.borrow().clone())
}

/// The bytes that the values of the run hold.
pub(crate) fn live() -> usize {
    METER.with(|m| m.borrow().as_ref().map_or(0, |m| m.load(Ordering::Relaxed)))
}

/// Whether `bytes` more fit in the run's memory.
pub(crate) fn fits(bytes: usize) -> bool {
    live().saturating_add(bytes) <= MEMORY
}

/// What a value holds, in bytes.
pub(crate) trait Weight {
    fn weight(&self) -> usize;
}

impl Weight for () {
    fn weight(&self) -> usize {
        0
    }
}

impl Weight for String {
    fn weight(&self) -> usize {
        self.len()
    }
}

impl<T> Weight for Vec<T> {
    fn weight(&self) -> usize {
        self.len() * std::mem::size_of::<T>()
    }
}

/// A value, weighed while it lives. It reads as what it holds, and changes only through
/// [`Counted::update`], which weighs it again.
#[derive(Debug)]
pub(crate) struct Counted<T: Weight> {
    inner: T,
    weight: usize,
    meter: Option<Meter>,
}

fn weigh(meter: Option<&Meter>, add: usize, sub: usize) {
    if let Some(m) = meter {
        if add >= sub {
            m.fetch_add(add - sub, Ordering::Relaxed);
        } else {
            m.fetch_sub(sub - add, Ordering::Relaxed);
        }
    }
}

impl<T: Weight> Counted<T> {
    pub(crate) fn new(inner: T) -> Self {
        let weight = OVERHEAD + inner.weight();
        let meter = meter();
        weigh(meter.as_ref(), weight, 0);
        Self {
            inner,
            weight,
            meter,
        }
    }

    /// A value that holds nothing on the heap, as the unit value, which no run's memory counts.
    pub(crate) fn empty(inner: T) -> Self {
        Self {
            inner,
            weight: 0,
            meter: None,
        }
    }

    pub(crate) fn get(&self) -> &T {
        &self.inner
    }

    /// Changes what it holds, and weighs it again.
    pub(crate) fn update<R>(&mut self, f: impl FnOnce(&mut T) -> R) -> R {
        let r = f(&mut self.inner);
        let weight = OVERHEAD + self.inner.weight();
        if self.meter.is_none() {
            // An empty value that grows is weighed from then on.
            self.meter = meter();
            weigh(self.meter.as_ref(), weight, 0);
        } else {
            weigh(self.meter.as_ref(), weight, self.weight);
        }
        self.weight = weight;
        r
    }
}

/// Memory that something other than a value takes, as a fiber's thread does, weighed while
/// this lives.
#[derive(Debug)]
pub(crate) struct Held {
    weight: usize,
    meter: Option<Meter>,
}

impl Held {
    pub(crate) fn new(weight: usize) -> Self {
        let meter = meter();
        weigh(meter.as_ref(), weight, 0);
        Self { weight, meter }
    }
}

impl Drop for Held {
    fn drop(&mut self) {
        weigh(self.meter.as_ref(), 0, self.weight);
    }
}

impl<E> Counted<Vec<E>> {
    /// Its elements, to change in place: their number stays, and so does its weight.
    pub(crate) fn slots(&mut self) -> &mut [E] {
        &mut self.inner
    }
}

impl<T: Weight> Deref for Counted<T> {
    type Target = T;

    fn deref(&self) -> &T {
        &self.inner
    }
}

impl<T: Weight + Clone> Clone for Counted<T> {
    fn clone(&self) -> Self {
        Self::new(self.inner.clone())
    }
}

impl<T: Weight> Drop for Counted<T> {
    fn drop(&mut self) {
        weigh(self.meter.as_ref(), 0, self.weight);
    }
}

#[cfg(test)]
mod tests {
    use std::sync::Arc;
    use std::sync::atomic::{AtomicUsize, Ordering};

    use stilt_hir::hir::Name;

    use crate::value::{Value, prelude};

    #[test]
    fn every_value_on_the_heap_is_weighed_while_it_lives() {
        let meter = Arc::new(AtomicUsize::new(0));
        super::use_meter(&meter);
        let unit = Value::unit();
        assert_eq!(
            meter.load(Ordering::Relaxed),
            0,
            "the unit value holds nothing"
        );
        let pair = Value::tuple(vec![Value::i64(1), unit]);
        let some = Value::variant(prelude("Some"), vec![pair]);
        let record = Value::record(prelude("Point"), vec![(Name::from("x"), some)]);
        // Three allocations, each two values or fewer and its share.
        let held = meter.load(Ordering::Relaxed);
        assert!(
            held >= 3 * super::OVERHEAD + 4 * size_of::<Value<'_>>(),
            "{held}"
        );
        drop(record);
        assert_eq!(
            meter.load(Ordering::Relaxed),
            0,
            "dropped values weigh nothing"
        );
    }
}
