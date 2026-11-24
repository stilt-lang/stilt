//! Handlers at run time (handlers.with and handlers.resuming).
//!
//! A `with` installs its handler as a node of a list, the innermost first, that a performance
//! searches for its effect: each context, the thread's stack or a body's own, has its list, and
//! a body's starts outside the `with` it belongs to. A handler is a data object: its kind, then
//! for each operation the hash of its name and its closure, which takes the box of the
//! arguments and gives its result in one word.
//!
//! A handler that resumes at once is called on the stack of the performance. One that takes
//! control and never resumes is too, and its value ends the `with`: the performance raises an
//! *abort*, which every `catch` passes on and the `with` takes, with the value, as a raise
//!. One whose bodies resume runs each body on a stack of its own
//! (`crate::fiber`): `resume(v)` switches back to the performance, which gives `v`, and the
//! body waits there until the `with`'s block ends and gives it the block's value, which the
//! body's value then replaces, innermost first. A body that a `with` leaves waiting, when its
//! block ends with a raise or a jump, is cancelled: its `resume` raises an abort that unwinds
//! it.
//!
//! Compiled code calls the performance, `resume` and the end of a `with` as closures, which
//! can raise, whose code is here ([`stilt_rt_effect_code`]).

mod bodies;

use std::cell::Cell;
use std::ptr::null_mut;
use std::sync::{Arc, OnceLock};

use bodies::{Message, Strand, body, copy_error, free, run};

use crate::abi::{Ret, call1};
use crate::fiber::Context;
use crate::object::{Header, data_field, drop as release, dup, lent_data};
use crate::tasks::Async;

/// The kinds of handlers: one that resumes at once, one that takes control and never resumes,
/// and one whose bodies resume.
const CONTROL: u64 = 1;
const RESUMES: u64 = 2;

/// The target of an abort that cancels a body waiting in its `resume`.
const CANCEL: usize = 1;

/// The target of an abort that stops code the sequential run never reaches, which waits for a
/// task that raised or stopped (`crate::std_task`): the task or scope that runs it takes it.
const UNREACHED: usize = 2;

/// The hash of `async`'s name, `std.prelude.async`, as `stilt_mir` hashes an effect's.
const ASYNC: u64 = 0x0a06_0b52_16f4_942b;

/// A handler installed by a `with`, which owns a reference to it, and the bodies of its
/// operations that resumed and wait for the block's value, the latest last.
#[derive(Debug)]
struct Node {
    effect: u64,
    handler: u64,
    next: *mut Node,
    suspended: Vec<*mut Strand>,
    /// For a handler of `async`, which one, with the tasks started under it on threads.
    tasks: Option<Async>,
}

thread_local! {
    /// The handlers installed on the running context.
    static CURRENT: Cell<*mut Node> = const { Cell::new(null_mut()) };
    /// The abort being raised: the node of its `with`, or [`CANCEL`], and the body's value.
    static ABORT: Cell<(usize, u64)> = const { Cell::new((0, 0)) };
}

/// Ends the `with` of `node` with a body's value, as an abort the performance raises, writing
/// zeros to the memory for an error of `words` words.
///
/// # Safety
///
/// `err` is null or points to room for `words` words.
unsafe fn abort(node: *mut Node, answer: u64, err: *mut u64, words: u64) -> Ret {
    ABORT.set((node as usize, answer));
    if !err.is_null() {
        // SAFETY: as the caller guarantees.
        unsafe { std::ptr::write_bytes(err, 0, words as usize) };
    }
    Ret::raise(0)
}

/// The nearest handler of `effect` installed on the running context.
fn find(loc: u64, effect: u64) -> *mut Node {
    let mut node = CURRENT.get();
    // SAFETY: the nodes of the list are those of `with`s that haven't ended.
    unsafe {
        while !node.is_null() && (*node).effect != effect {
            node = (*node).next;
        }
    }
    if node.is_null() {
        crate::panic::panic(
            loc,
            5,
            "an operation performed under no handler of its effect",
        );
    }
    node
}

/// The handler of `async` innermost on the running context, if a `with` installed one.
pub(crate) fn innermost_async() -> Option<Async> {
    let mut node = CURRENT.get();
    // SAFETY: the nodes of the list are those of `with`s that haven't ended.
    unsafe {
        while !node.is_null() {
            if let Some(tasks) = &(*node).tasks {
                return Some(tasks.clone());
            }
            node = (*node).next;
        }
    }
    None
}

/// Raises the abort that stops code the sequential run never reaches, through every frame up
/// to the task or the scope that runs it ([`take_unreached`]).
pub(crate) fn abort_unreached() -> Ret {
    ABORT.set((UNREACHED, 0));
    Ret::raise(0)
}

/// Whether `r` raises the abort of [`abort_unreached`], which it then ends.
pub(crate) fn take_unreached(r: Ret) -> bool {
    if r.raised != 0 && ABORT.get().0 == UNREACHED {
        ABORT.set((0, 0));
        return true;
    }
    false
}

/// The closure of the operation whose name hashes to `op` in a handler.
///
/// # Safety
///
/// `handler` is a live handler that implements the operation.
unsafe fn operation(handler: *mut Header, op: u64) -> u64 {
    // SAFETY: as the caller guarantees: after its kind, a handler holds pairs of a hash and
    // a closure.
    unsafe {
        let len = crate::object::data_len(handler);
        (1..len)
            .step_by(2)
            .find(|&i| *data_field(handler, i) == op)
            .map_or(0, |i| *data_field(handler, i + 1))
    }
}

/// Performs operation `op` of `effect`, on the box of its arguments, which it borrows. An error
/// of `words` words, more than one, goes to `err`.
///
/// # Safety
///
/// Compiled code calls it as the code of a closure of [`codes`], inside a `with` that handles
/// `effect`: `op` is the hash of one of the effect's operations, `args` a live box of its
/// arguments, and `err` null or room for `words` words.
unsafe extern "C" fn perform(
    loc: u64,
    _closure: u64,
    effect: u64,
    op: u64,
    args: u64,
    words: u64,
    err: u64,
) -> Ret {
    let err = err as usize as *mut u64;
    let node = find(loc, effect);
    // SAFETY: the node's handler is alive while its `with` runs, and implements its effect's
    // operations; the bodies made here are boxed, and own a reference to the arguments.
    unsafe {
        let handler = (*node).handler as *mut Header;
        let kind = *data_field(handler, 0);
        let closure = operation(handler, op);
        if kind != RESUMES {
            let site = CURRENT.replace((*node).next);
            let r = call1(loc, closure, args, err);
            CURRENT.set(site);
            return if kind == CONTROL && r.raised == 0 {
                abort(node, r.value, err, words)
            } else {
                r
            };
        }
        dup(args);
        let s = Box::into_raw(Box::new(Strand::new()));
        (*s).context = Context::new(body, s as usize);
        (*s).evidence = (*node).next;
        (*s).call = [loc, closure, args];
        (*s).err = vec![0; if words > 1 { words as usize } else { 0 }];
        match run(s) {
            Message::Resumed(v) => {
                (*node).suspended.push(s);
                Ret::ok(v)
            }
            Message::Ended(r) => {
                let r = if r.raised == 0 {
                    abort(node, r.value, err, words)
                } else {
                    copy_error(s, err);
                    r
                };
                free(s);
                r
            }
            _ => std::process::abort(),
        }
    }
}

/// Ends the `with` of `node` whose block's value is `x`: each body that waits, the latest
/// first, takes the value and replaces it with its own, then the handler is removed.
///
/// # Safety
///
/// Compiled code calls it as the code of a closure of [`codes`]: `node` is the innermost
/// handler of the running context, `x` a word of its block's type, and `err` null or room for
/// the error a body may raise.
unsafe extern "C" fn finish(
    _loc: u64,
    _closure: u64,
    node: u64,
    x: u64,
    _words: u64,
    err: u64,
) -> Ret {
    let err = err as usize as *mut u64;
    let node = node as *mut Node;
    let mut x = x;
    // SAFETY: the `with` of `node` runs, and its bodies wait.
    unsafe {
        while let Some(s) = (*node).suspended.pop() {
            (*s).message = Message::Answer(x);
            let ended = run(s);
            if let Message::Ended(r) = ended
                && r.raised != 0
            {
                copy_error(s, err);
                free(s);
                leave(node);
                return r;
            }
            if let Message::Ended(r) = ended {
                x = r.value;
            }
            free(s);
        }
        leave(node);
    }
    Ret::ok(x)
}

/// Removes the handler of `node`, cancelling the bodies that wait, the latest first.
///
/// # Safety
///
/// `node` is the innermost handler of the running context.
unsafe fn leave(node: *mut Node) {
    let raising = ABORT.get();
    // SAFETY: as the caller guarantees; the node is boxed.
    unsafe {
        while let Some(s) = (*node).suspended.pop() {
            (*s).message = Message::Cancel;
            run(s);
            free(s);
        }
        ABORT.set(raising);
        let node = Box::from_raw(node);
        // A `with` of `task.threads()` ends once its tasks have (tasks.with-waits).
        if let Some(Async::Threads(group)) = &node.tasks {
            group.wait();
        }
        CURRENT.set(node.next);
        release(node.handler);
    }
}

/// Installs `handler` for `effect`, and gives its node.
///
/// # Safety
///
/// `handler` is a live handler.
#[unsafe(no_mangle)]
pub(crate) unsafe extern "C" fn stilt_rt_with_enter(effect: u64, handler: u64) -> u64 {
    // SAFETY: as the caller guarantees.
    unsafe { dup(handler) };
    let next = CURRENT.get();
    let tasks = (effect == ASYNC).then(|| {
        // SAFETY: as the caller guarantees; a handler of `async` comes from `std.task`.
        // WebAssembly has one thread, where `task.threads()` runs each task in order as
        // `task.sequential()` does (wasm.tasks-in-order).
        if cfg!(not(target_family = "wasm")) && unsafe { crate::std_task::is_threads(handler) } {
            Async::Threads(Arc::default())
        } else {
            Async::Sequential
        }
    });
    let node = Box::into_raw(Box::new(Node {
        effect,
        handler,
        next,
        suspended: Vec::new(),
        tasks,
    }));
    CURRENT.set(node);
    node as u64
}

/// Removes the handler of a `with` that its block leaves with a raise or a jump.
///
/// # Safety
///
/// `node` is the innermost handler of the running context.
#[unsafe(no_mangle)]
pub(crate) unsafe extern "C" fn stilt_rt_with_leave(node: u64) {
    // SAFETY: as the caller guarantees.
    unsafe { leave(node as *mut Node) }
}

/// Whether the raise going on is an abort.
#[unsafe(no_mangle)]
pub(crate) extern "C" fn stilt_rt_aborting() -> u64 {
    u64::from(ABORT.get().0 != 0)
}

/// Whether the raise going on is an abort that ends the `with` of `node`.
#[unsafe(no_mangle)]
pub(crate) extern "C" fn stilt_rt_aborting_to(node: u64) -> u64 {
    u64::from(ABORT.get().0 == node as usize)
}

/// The value of the body that aborted, which ends the abort.
#[unsafe(no_mangle)]
pub(crate) extern "C" fn stilt_rt_abort_take() -> u64 {
    ABORT.replace((0, 0)).1
}

/// The closures whose code performs an operation, resumes, and ends a `with`, in that order:
/// static objects, which no count frees.
fn codes() -> &'static [u64; 3] {
    static CODES: OnceLock<[u64; 3]> = OnceLock::new();
    CODES.get_or_init(|| {
        let code: [*const (); 3] = [
            perform as *const (),
            bodies::resume as *const (),
            finish as *const (),
        ];
        code.map(|c| {
            let slot: &'static mut u64 = Box::leak(Box::new(c as u64));
            let memory: &'static mut [u64] = Box::leak(vec![0u64; 4].into_boxed_slice());
            lent_data(memory, &[std::ptr::from_mut(slot) as u64], |_| false) as u64
        })
    })
}

/// The closure whose code performs (0), resumes (1) or ends a `with` (2).
#[unsafe(no_mangle)]
pub(crate) extern "C" fn stilt_rt_effect_code(which: u64) -> u64 {
    codes()[which as usize]
}

/// The functions of this module that compiled code calls, by name.
pub(crate) fn symbols() -> Vec<(&'static str, *const u8)> {
    crate::exports![
        stilt_rt_with_enter,
        stilt_rt_with_leave,
        stilt_rt_aborting,
        stilt_rt_aborting_to,
        stilt_rt_abort_take,
        stilt_rt_effect_code,
    ]
}
