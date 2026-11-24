//! The threads that run a program's code, and their stacks. Each asks for 1 GiB, enough for a
//! recursion millions of calls deep, which the system reserves and gives memory only as calls
//! reach it, so a thread that never goes deep costs no more than with a small stack. A system
//! that counts what it reserves against a limit, as Linux does with strict overcommit, may refuse
//! that much, and the thread then gets the largest of the smaller stacks that it grants, so the
//! program starts and only its deepest recursions end with a stack overflow.

use std::io;
use std::sync::{Arc, Mutex, PoisonError};
use std::thread::{Builder, JoinHandle};

/// The size of the stack that each thread that runs the program's code asks for first.
pub(crate) const STACK: usize = 1024 * 1024 * 1024;

/// The sizes asked for in turn, the last above the stack that program.recursion-depth needs.
const SIZES: [usize; 3] = [STACK, 256 * 1024 * 1024, 16 * 1024 * 1024];

/// Starts a thread named `name` that runs `f`, on the largest stack of [`SIZES`] that the system
/// grants, or gives the error of the smallest.
pub(crate) fn spawn<F, T>(name: &str, f: F) -> io::Result<JoinHandle<T>>
where
    F: FnOnce() -> T + Send + 'static,
    T: Send + 'static,
{
    // A refused thread drops what it was given, so it gets `f` through a slot that only the
    // thread that starts empties.
    let slot = Arc::new(Mutex::new(Some(f)));
    let mut refused = None;
    for size in SIZES {
        let theirs = Arc::clone(&slot);
        let started = Builder::new()
            .name(name.to_owned())
            .stack_size(size)
            .spawn(move || {
                let f = theirs
                    .lock()
                    .unwrap_or_else(PoisonError::into_inner)
                    .take()
                    .expect("only the thread that starts takes the function");
                f()
            });
        match started {
            Ok(handle) => return Ok(handle),
            Err(error) => refused = Some(error),
        }
    }
    Err(refused.expect("SIZES isn't empty"))
}

#[cfg(test)]
mod tests {
    #[test]
    fn a_thread_runs_its_function_once() {
        let handle = super::spawn("test", || 6 * 7).expect("a thread");
        assert_eq!(handle.join().ok(), Some(42));
    }
}
