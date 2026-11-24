//! The stacks of the threads that check and compile. Checking recurses as deep as code nests,
//! which lexical.nesting bounds for brackets but nothing bounds for a long sum or a run of unary
//! operators, so each thread asks for 1 GiB, which the system reserves and gives memory only as
//! the recursion reaches it: a thread that never goes deep costs no more than with a small stack.
//! A system that counts what it reserves against a limit, as Linux does with strict overcommit,
//! may refuse that much, and the thread then gets the largest of the smaller stacks it grants.

use std::io;
use std::sync::{Arc, Mutex, PoisonError};
use std::thread::{Builder, Scope, ScopedJoinHandle};

/// The sizes asked for in turn.
const STACKS: [usize; 3] = [1 << 30, 256 << 20, 16 << 20];

/// Starts a thread of `scope` that runs `f`, on the largest stack of [`STACKS`] that the system
/// grants, or gives the error of the smallest.
pub(crate) fn spawn<'scope, F, T>(
    scope: &'scope Scope<'scope, '_>,
    f: F,
) -> io::Result<ScopedJoinHandle<'scope, T>>
where
    F: FnOnce() -> T + Send + 'scope,
    T: Send + 'scope,
{
    // A refused thread drops what it was given, so it gets `f` through a slot that only the
    // thread that starts empties.
    let slot = Arc::new(Mutex::new(Some(f)));
    let mut refused = None;
    for size in STACKS {
        let theirs = Arc::clone(&slot);
        let started = Builder::new()
            .stack_size(size)
            .spawn_scoped(scope, move || {
                let f = (theirs.lock().unwrap_or_else(PoisonError::into_inner).take())
                    .expect("only the thread that starts takes the function");
                f()
            });
        match started {
            Ok(handle) => return Ok(handle),
            Err(error) => refused = Some(error),
        }
    }
    Err(refused.expect("STACKS isn't empty"))
}

/// Runs `f` on a thread of its own with a stack as large as [`spawn`] gives, and returns what it
/// returns, or goes on with its panic.
///
/// # Panics
///
/// When the system starts no thread at all.
pub fn deep<T: Send>(f: impl FnOnce() -> T + Send) -> T {
    std::thread::scope(
        |scope| match spawn(scope, f).expect("a thread for the command").join() {
            Ok(value) => value,
            Err(panic) => std::panic::resume_unwind(panic),
        },
    )
}

#[cfg(test)]
mod tests {
    #[test]
    fn a_deep_thread_runs_its_function_once() {
        assert_eq!(super::deep(|| 6 * 7), 42);
    }

    #[test]
    fn a_deep_thread_recurses_past_a_main_thread_s_stack() {
        fn depth(n: u64) -> u64 {
            let frame = std::hint::black_box([n; 64]);
            if n == 0 {
                0
            } else {
                1 + depth(n - 1) + frame[0] - n
            }
        }
        // 200,000 frames of more than 512 bytes are past an 8 MiB stack.
        assert_eq!(super::deep(|| depth(200_000)), 200_000);
    }
}
