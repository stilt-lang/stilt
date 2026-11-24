//! Costly work across the machine's cores while the calling thread works alongside it, taking
//! what each item's work gives early as soon as it is given, as a build takes what translating
//! a function asked while the function is still being compiled (goal compile-time-code-rebuilds).

use std::panic::{self, AssertUnwindSafe};
use std::sync::{Condvar, Mutex, PoisonError};
use std::thread;

use super::{stacks, threads};

/// What each item's work gave early, which the calling thread waits for.
#[derive(Debug)]
pub struct Early<E> {
    slots: Mutex<Vec<Slot<E>>>,
    given: Condvar,
}

#[derive(Debug)]
enum Slot<E> {
    Pending,
    Given(E),
    /// The work panicked before it gave anything, or what it gave was taken.
    Gone,
}

impl<E> Early<E> {
    /// What item `i`'s work gives early, once it gives it, or `None` when its work panicked
    /// before it did, or what it gave was taken already.
    ///
    /// # Panics
    ///
    /// Panics when `i` is no item's index.
    pub fn wait(&self, i: usize) -> Option<E> {
        let mut slots = self.slots.lock().unwrap_or_else(PoisonError::into_inner);
        while matches!(slots[i], Slot::Pending) {
            slots = self
                .given
                .wait(slots)
                .unwrap_or_else(PoisonError::into_inner);
        }
        match std::mem::replace(&mut slots[i], Slot::Gone) {
            Slot::Given(e) => Some(e),
            Slot::Pending | Slot::Gone => None,
        }
    }

    /// Fills item `i`'s slot, unless its work gave something already.
    fn give(&self, i: usize, slot: Slot<E>) {
        let mut slots = self.slots.lock().unwrap_or_else(PoisonError::into_inner);
        if matches!(slots[i], Slot::Pending) {
            slots[i] = slot;
        }
        self.given.notify_all();
    }
}

/// Runs `work` on each of `items` across up to a thread each, as [`super::map_costly`] does,
/// while `alongside` runs on the calling thread. Each item's work may give a value early, by
/// the function it is given, which `alongside` takes by the item's index from the [`Early`] it
/// is given, waiting for it. Returns what `alongside` returns, and each item's result, in the
/// items' order.
///
/// # Panics
///
/// Panics when the system can't start a thread, and with the panic of any item's work, once
/// `alongside` returns: the items not yet started are given up, so that `alongside` waits for
/// nothing that never comes.
pub fn map_costly_alongside<T, E, U, R>(
    items: Vec<T>,
    work: impl Fn(T, &dyn Fn(E)) -> U + Sync,
    alongside: impl FnOnce(&Early<E>) -> R,
) -> (R, Vec<U>)
where
    T: Send,
    E: Send,
    U: Send,
{
    let early = Early {
        slots: Mutex::new((0..items.len()).map(|_| Slot::Pending).collect()),
        given: Condvar::new(),
    };
    let threads = threads().min(items.len());
    let queue = Mutex::new(items.into_iter().enumerate());
    thread::scope(|scope| {
        let workers: Vec<_> = (0..threads)
            .map(|_| {
                let (queue, work, early) = (&queue, &work, &early);
                stacks::spawn(scope, move || worker(queue, work, early))
                    .expect("a thread for costly work")
            })
            .collect();
        let alongside = alongside(&early);
        let mut done: Vec<(usize, U)> = (workers.into_iter())
            .flat_map(|w| w.join().unwrap_or_else(|e| panic::resume_unwind(e)))
            .collect();
        done.sort_unstable_by_key(|&(i, _)| i);
        (alongside, done.into_iter().map(|(_, u)| u).collect())
    })
}

/// A worker: the next item of `queue` until there are none, each item's results.
fn worker<T, E, U>(
    queue: &Mutex<impl Iterator<Item = (usize, T)>>,
    work: &(impl Fn(T, &dyn Fn(E)) -> U + Sync),
    early: &Early<E>,
) -> Vec<(usize, U)> {
    let mut out = Vec::new();
    loop {
        let next = queue.lock().unwrap_or_else(PoisonError::into_inner).next();
        let Some((i, item)) = next else {
            return out;
        };
        let give = |e| early.give(i, Slot::Given(e));
        match panic::catch_unwind(AssertUnwindSafe(|| work(item, &give))) {
            Ok(u) => out.push((i, u)),
            Err(e) => {
                early.give(i, Slot::Gone);
                let mut queue = queue.lock().unwrap_or_else(PoisonError::into_inner);
                for (j, _) in queue.by_ref() {
                    early.give(j, Slot::Gone);
                }
                drop(queue);
                panic::resume_unwind(e)
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use std::time::Duration;

    use super::map_costly_alongside;

    #[test]
    fn the_calling_thread_takes_each_early_value_in_its_own_order() {
        // Each item gives its square at once, then takes longer the earlier it is, while the
        // calling thread takes the squares from the last item to the first.
        let items: Vec<u64> = (0..6).collect();
        let (taken, done) = map_costly_alongside(
            items,
            |i, give| {
                give(i * i);
                std::thread::sleep(Duration::from_millis(30 - 5 * i));
                i + 100
            },
            |early| (0..6).rev().map(|i| early.wait(i)).collect::<Vec<_>>(),
        );
        let squares: Vec<Option<u64>> = [25, 16, 9, 4, 1, 0].into_iter().map(Some).collect();
        assert_eq!(taken, squares);
        assert_eq!(done, [100, 101, 102, 103, 104, 105]);
    }

    #[test]
    fn a_value_is_taken_once() {
        let (taken, _) = map_costly_alongside(
            vec![7],
            |i, give| give(i),
            |early| (early.wait(0), early.wait(0)),
        );
        assert_eq!(taken, (Some(7), None));
    }
}
