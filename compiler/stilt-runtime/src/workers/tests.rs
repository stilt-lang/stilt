//! The number of threads that tests give the calls of `std.par`, and the pool's own tests.

use std::cell::Cell;
use std::sync::atomic::{AtomicUsize, Ordering};

use super::Call;

thread_local! {
    /// The number of threads that the calls the current thread makes run on, when a test sets it.
    static THREADS: Cell<Option<usize>> = const { Cell::new(None) };
}

/// The number of threads a test gave the current thread's calls.
pub(super) fn threads() -> Option<usize> {
    THREADS.get()
}

/// Runs `f` with the calls that the current thread makes, but not those of their parts, on `n`
/// threads.
pub(crate) fn on_threads<T>(n: usize, f: impl FnOnce() -> T) -> T {
    let before = THREADS.replace(Some(n));
    let result = f();
    THREADS.set(before);
    result
}

/// The thread counts that tests try: one, two, and more than most machines have cores.
pub(crate) const COUNTS: [usize; 4] = [1, 2, 3, 16];

#[test]
fn every_part_runs_once_and_finishes_in_order() {
    for n in COUNTS {
        on_threads(n, || {
            let runs: Vec<AtomicUsize> = (0..50).map(|_| AtomicUsize::new(0)).collect();
            let run = |k: usize| {
                runs[k].fetch_add(1, Ordering::SeqCst);
            };
            let mut call = Call::start(runs.len(), &run);
            for (k, ran) in runs.iter().enumerate() {
                call.finish(k);
                assert_eq!(ran.load(Ordering::SeqCst), 1, "part {k} on {n} threads");
            }
        });
    }
}

#[test]
fn calls_inside_parts_end_however_few_threads_there_are() {
    for n in COUNTS {
        on_threads(n, || {
            let total = AtomicUsize::new(0);
            let outer = |_: usize| {
                let inner = |k: usize| {
                    total.fetch_add(k, Ordering::SeqCst);
                };
                let mut call = Call::start(10, &inner);
                for k in 0..10 {
                    call.finish(k);
                }
            };
            let mut call = Call::start(10, &outer);
            for k in 0..10 {
                call.finish(k);
            }
            drop(call);
            assert_eq!(total.load(Ordering::SeqCst), 10 * 45, "on {n} threads");
        });
    }
}

#[test]
fn on_two_threads_the_parts_after_the_callers_run_at_once() {
    use std::time::{Duration, Instant};
    on_threads(2, || {
        let started = AtomicUsize::new(0);
        let met = AtomicUsize::new(0);
        // The caller's part takes long enough for the workers to take the other two, which
        // each wait for the other: they meet only when two workers run them at once.
        let run = |k: usize| {
            if k == 0 {
                std::thread::sleep(Duration::from_millis(50));
                return;
            }
            started.fetch_add(1, Ordering::SeqCst);
            let deadline = Instant::now() + Duration::from_secs(5);
            while started.load(Ordering::SeqCst) < 2 && Instant::now() < deadline {
                std::hint::spin_loop();
            }
            if started.load(Ordering::SeqCst) == 2 {
                met.fetch_add(1, Ordering::SeqCst);
            }
        };
        let mut call = Call::start(3, &run);
        for k in 0..3 {
            call.finish(k);
        }
        drop(call);
        assert_eq!(
            met.load(Ordering::SeqCst),
            2,
            "the two parts ran one after the other"
        );
    });
}
