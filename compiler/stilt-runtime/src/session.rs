//! The values of a REPL session, and the runs of its inputs (repl.answers, repl.running-inputs and
//! repl.bindings-across-edits).
//!
//! A session keeps each binding's value as the words of its type's layout, each heap word
//! holding one reference, which the value releases when the session drops it. An input runs on
//! a frame: the words of the bindings, in order, which the input borrows, then room for the
//! words of the values that a `let` binds, which its entry writes and the session then owns.

use crate::entry::{Entry, Program, no_entry, prepare};
use crate::object;
use crate::watch::{Evaluated, run_input};

/// Prepares this process to run the inputs of a REPL session, whose program's files have the
/// paths `files`: reports of panics name them, and a stack overflow ends the process. It may be
/// called again when the program's files change.
pub fn prepare_session(files: Vec<String>) {
    prepare(Program {
        entry: no_entry,
        files,
        args: Vec::new(),
        check_leaks: false,
        with_errors: false,
    });
}

/// A value that a session keeps.
#[derive(Debug)]
pub struct Value {
    words: Vec<u64>,
    /// Whether each word is a heap word.
    heap: Vec<bool>,
}

impl Drop for Value {
    fn drop(&mut self) {
        for (&word, &heap) in self.words.iter().zip(&self.heap) {
            if heap {
                // SAFETY: each heap word of a value holds one reference of its own, which
                // nothing reads after.
                unsafe { object::drop(word) };
            }
        }
    }
}

/// Runs an input's entry on the words of `bindings`, in order, with room after them for the
/// values a `let` binds, of which `binds` gives the heapness of each word, as the entry was
/// compiled for. Gives how the input ended and, when its entry returned, the values it bound.
#[must_use]
pub fn evaluate(entry: Entry, bindings: &[&Value], binds: &[Vec<bool>]) -> (Evaluated, Vec<Value>) {
    let mut frame: Vec<u64> = bindings
        .iter()
        .flat_map(|v| v.words.iter().copied())
        .collect();
    let start = frame.len();
    frame.resize(start + binds.iter().map(Vec::len).sum::<usize>(), 0);
    let evaluated = run_input(entry, frame.as_mut_ptr() as u64);
    let mut made = Vec::new();
    // The entry writes the bound values only once the input's body has returned.
    if matches!(evaluated, Evaluated::Value(_)) {
        let mut at = start;
        for heap in binds {
            let words = frame[at..at + heap.len()].to_vec();
            at += heap.len();
            made.push(Value {
                words,
                heap: heap.clone(),
            });
        }
    }
    (evaluated, made)
}
