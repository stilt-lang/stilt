//! The bodies of handlers that resume, each on a context of its own (`crate::fiber`), and the
//! switches between a body and the context that runs it: a performance starts a body, which
//! runs until it resumes or ends, and the end of its `with` runs it again, to its end, with the
//! value of the rest of the block, or cancels it (handlers.resuming).

use std::cell::{Cell, UnsafeCell};
use std::ptr::null_mut;

use super::{ABORT, CANCEL, CURRENT, Node};
use crate::abi::Ret;
use crate::fiber::{self, Context};
use crate::object::drop as release;

/// What a switch to a body or back carries.
#[derive(Clone, Copy, Debug)]
pub(super) enum Message {
    Empty,
    /// The body resumed with this value.
    Resumed(u64),
    /// The body ended with this value, or raised.
    Ended(Ret),
    /// The value of the rest of the block, for a waiting body's `resume`.
    Answer(u64),
    Cancel,
}

/// A context that code runs on, with the handlers installed on it while it doesn't run, and
/// for a body, what it calls and the context it switches back to.
#[derive(Debug)]
pub(super) struct Strand {
    pub(super) context: Context,
    pub(super) evidence: *mut Node,
    waiter: *mut Strand,
    pub(super) message: Message,
    /// The location, the closure and the box of the arguments of the body's call.
    pub(super) call: [u64; 3],
    /// Room for the words of an error of several words that the body raises.
    pub(super) err: Vec<u64>,
}

impl Strand {
    pub(super) fn new() -> Self {
        Self {
            context: Context::default(),
            evidence: null_mut(),
            waiter: null_mut(),
            message: Message::Empty,
            call: [0; 3],
            err: Vec::new(),
        }
    }
}

thread_local! {
    /// The running context, or null for the thread's own.
    static RUNNING: Cell<*mut Strand> = const { Cell::new(null_mut()) };
    static THREAD: UnsafeCell<Strand> = UnsafeCell::new(Strand::new());
}

fn running() -> *mut Strand {
    let r = RUNNING.get();
    if r.is_null() {
        THREAD.with(UnsafeCell::get)
    } else {
        r
    }
}

/// Switches from the running context `from` to `to`, with `to`'s handlers.
///
/// # Safety
///
/// `from` is the running context, and `to` one that waits.
#[cfg_attr(
    target_family = "wasm",
    inline(never),
    unsafe(export_name = "stilt_rt_transfer")
)]
unsafe fn transfer(from: *mut Strand, to: *mut Strand, last: bool) {
    // SAFETY: as the caller guarantees.
    unsafe {
        (*from).evidence = CURRENT.get();
        CURRENT.set((*to).evidence);
        RUNNING.set(to);
        fiber::switch(&raw mut (*from).context, &raw mut (*to).context, last);
    }
}

/// Runs the body `s` until it switches back, and gives what it says.
///
/// # Safety
///
/// `s` is a body that waits, or a new one.
pub(super) unsafe fn run(s: *mut Strand) -> Message {
    let me = running();
    // SAFETY: as the caller guarantees.
    unsafe {
        (*s).waiter = me;
        transfer(me, s, false);
        std::mem::replace(&mut (*s).message, Message::Empty)
    }
}

/// Gives back a body that will never run again.
///
/// # Safety
///
/// `s` is a body that ended.
pub(super) unsafe fn free(s: *mut Strand) {
    // SAFETY: as the caller guarantees, and bodies are boxed.
    let mut s = unsafe { Box::from_raw(s) };
    s.context.release();
}

/// Where a body starts: it calls its operation's closure, then switches back for the last time,
/// which on the native targets never returns.
///
/// # Safety
///
/// It is the entry of a body's context, and `arg` the body, which a performance made.
#[cfg_attr(
    target_family = "wasm",
    inline(never),
    unsafe(export_name = "stilt_rt_body")
)]
pub(super) unsafe extern "C" fn body(arg: usize) {
    fiber::started();
    let s = arg as *mut Strand;
    // SAFETY: the performance made the body, which lives until it ends, with a closure of one
    // parameter and a box of its arguments, which the body owns a reference to. The closure's
    // code is called here, rather than by `call1`, since the call is on the body's frames
    // when it switches back, which WebAssembly instruments (`crate::fiber`).
    unsafe {
        let [loc, closure, args] = (*s).call;
        let err = if (*s).err.is_empty() {
            0
        } else {
            (*s).err.as_mut_ptr() as u64
        };
        let r = crate::abi::code1(closure)(loc, closure, args, err);
        release(args);
        (*s).message = Message::Ended(r);
        transfer(s, (*s).waiter, true);
    }
    #[cfg(not(target_family = "wasm"))]
    std::process::abort()
}

/// Copies the error of several words that a body raised to the memory of its caller.
///
/// # Safety
///
/// `err` is null or points to room for the body's error.
pub(super) unsafe fn copy_error(s: *mut Strand, err: *mut u64) {
    // SAFETY: as the caller guarantees.
    unsafe {
        let words = &(*s).err;
        if !err.is_null() && !words.is_empty() {
            std::ptr::copy_nonoverlapping(words.as_ptr(), err, words.len());
        }
    }
}

/// `resume(v)` in the running body, which gives `v` to its performance and waits for the value
/// of the rest of the block, or raises the abort that cancels it.
///
/// # Safety
///
/// Compiled code calls it as the code of a closure of `codes`, in the body of an operation of a
/// handler whose bodies resume (handlers.resuming).
#[cfg_attr(
    target_family = "wasm",
    inline(never),
    unsafe(export_name = "stilt_rt_resume")
)]
pub(super) unsafe extern "C" fn resume(_loc: u64, _closure: u64, v: u64, _err: u64) -> Ret {
    let s = running();
    // SAFETY: `resume` runs in a body (handlers.resuming), whose waiter is its performance.
    unsafe {
        (*s).message = Message::Resumed(v);
        transfer(s, (*s).waiter, false);
        if let Message::Answer(x) = std::mem::replace(&mut (*s).message, Message::Empty) {
            return Ret::ok(x);
        }
        ABORT.set((CANCEL, 0));
        Ret::raise(0)
    }
}
