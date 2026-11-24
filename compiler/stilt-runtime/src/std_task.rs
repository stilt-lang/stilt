//! The tasks of `std.task` (tasks.std-task). A program means what its run under `task.sequential()`
//! does (tasks.sequential-run): there `spawn` runs the task's function to its end before it
//! returns, and `await` gives the value it ended with, as often as it is called. Under
//! `task.threads()` `spawn` gives the function a deep copy of what it captures (`crate::object`'s
//! `copy`) and runs it on a thread (`crate::tasks`), which writes, reads and ends in the sequential
//! order (tasks.same-output-under-every-handler), and `await` waits for it. A task started inside a
//! `when`'s block, or by code the sequential run never reaches, runs where it starts.
//!
//! A `Task<T>` is a data object: the value the task ended with, in the one word that holds it
//! where a type parameter stands, its box for a value of several words, and for a task on a
//! thread, its [`State`], which the task's thread fills, and which the handle lets go when it
//! goes. A handle that another thread reaches is shared, and so is its value, once there is one.
//! Both handlers are data objects of the kind of a handler that resumes at once and no
//! operation (`crate::effects`), told apart by their tag.

use std::sync::{Arc, Condvar, Mutex, PoisonError};

use crate::abi::{Ret, address};
use crate::map::{dup_words, words_of};
use crate::object::{DATA, Header, SHARED, alloc_data, data_field, data_field_is_heap, dup};
use crate::object::{deep_copy, set_masks, share_within};
use crate::shape::Shape;
use crate::tasks::{self, Group};

/// The tag of a task's handle.
const TASK: u16 = u16::MAX - 1;

/// The tag of `task.threads()`.
const THREADS: u16 = 1;

/// The fields of a task's handle.
const VALUE: usize = 0;
const STATE: usize = 1;

// Compiled code takes every argument as a word, an address among them (`crate::abi`).
type Code0 = unsafe extern "C" fn(u64, u64, u64) -> Ret;
type Code0Out = unsafe extern "C" fn(u64, u64, u64, u64) -> Ret;

/// How a task on a thread stands.
#[derive(Debug, Default)]
struct Status {
    /// Whether it ended with a value, `Some(false)` when it ended without one: it raised, or
    /// stopped as code the sequential run never reaches.
    ended: Option<bool>,
    /// Whether its handle has gone, so that its value is dropped once it ends.
    orphaned: bool,
    /// Whether another thread reaches its handle, so that its value is shared.
    crossed: bool,
}

/// What a task's thread tells those that wait for it.
#[derive(Debug, Default)]
pub(crate) struct State {
    status: Mutex<Status>,
    ended: Condvar,
}

/// Whether an object is a task's handle.
///
/// # Safety
///
/// `object` is alive.
pub(crate) unsafe fn is_task(object: *mut Header) -> bool {
    // SAFETY: as the caller guarantees.
    unsafe { (*object).kind == DATA && (*object).tag == TASK }
}

/// The state of a task's handle, or null for a task that ended where it started.
///
/// # Safety
///
/// `task` is a live task's handle.
unsafe fn state_of(task: *mut Header) -> *const State {
    // SAFETY: the caller passes a live task's handle.
    unsafe { *data_field(task, STATE) as *const State }
}

/// A task's handle, holding no value yet.
pub(crate) fn handle(state: Option<&Arc<State>>) -> *mut Header {
    let task = alloc_data(2, TASK);
    // SAFETY: the object was just allocated with two fields, scalars until a value is stored;
    // the handle owns a reference to the state.
    unsafe {
        *data_field(task, VALUE) = 0;
        *data_field(task, STATE) = state.map_or(0, |s| Arc::into_raw(Arc::clone(s)) as u64);
        set_masks(task, |_| 0);
    }
    task
}

/// Stores `value`, of the shape `shape`, in a handle that only the current thread reaches.
///
/// # Safety
///
/// `task` is a live task's handle that holds no value and that no other thread reaches, and the
/// handle takes the reference that `value` owns.
unsafe fn store(task: *mut Header, value: u64, shape: Shape) {
    let heap = shape.heap() || shape.words() > 1;
    // SAFETY: as the caller guarantees.
    unsafe {
        *data_field(task, VALUE) = value;
        set_masks(task, |_| u64::from(heap));
    }
}

/// A task that ended with `value`, of the shape `shape`, in the one word that holds it, whose
/// reference it takes.
pub(crate) fn ended(value: u64, shape: Shape) -> Ret {
    let task = handle(None);
    // SAFETY: the handle was just made.
    unsafe { store(task, value, shape) };
    Ret::ok(task as u64)
}

/// The handle of a task that code the sequential run never reaches starts, which never runs:
/// an `await` of it stops that code.
pub(crate) fn unreached() -> Ret {
    let state = Arc::new(State::default());
    state
        .status
        .lock()
        .unwrap_or_else(PoisonError::into_inner)
        .ended = Some(false);
    Ret::ok(handle(Some(&state)) as u64)
}

/// Calls a closure of no parameters that gives a value of the shape `shape`, and gives its
/// value in one word, or what it raises, an error of several words to `err`.
///
/// # Safety
///
/// `f` is a live closure of no parameters that gives a value of the shape `shape`, and `err`
/// is null or room for the error it raises.
pub(crate) unsafe fn call(loc: u64, f: u64, shape: Shape, err: *mut u64) -> Ret {
    // SAFETY: a closure's field 0 holds the address of its code's slot, which holds the address
    // of the code, which takes the closure, `out` for a result of several words, and the memory
    // for an error of several words.
    unsafe {
        let code = *(*data_field(f as *mut Header, 0) as *const u64) as *const ();
        if shape.words() > 1 {
            let mut words = vec![0u64; shape.words()];
            let call: Code0Out = std::mem::transmute(code);
            let r = call(loc, f, address(words.as_mut_ptr()), address(err));
            if r.raised != 0 {
                return r;
            }
            return Ret::ok(crate::list::box_of(&words, shape));
        }
        let call: Code0 = std::mem::transmute(code);
        call(loc, f, address(err))
    }
}

/// `task.spawn(f)`: under `task.threads()`, starts `f` on a thread; otherwise runs it to its
/// end, passing on the abort that stops it if it is code the sequential run never reaches.
///
/// # Safety
///
/// `f` is a live closure of no parameters, which gives a value of shape `shape`. Like every
/// call whose row holds `async`, it is passed memory for an error, which an abort leaves
/// unused.
#[unsafe(no_mangle)]
pub(crate) unsafe extern "C" fn stilt_std_task_spawn(
    loc: u64,
    shape: u64,
    f: u64,
    _err: u64,
) -> Ret {
    let shape = Shape(shape);
    if tasks::unreached() {
        return unreached();
    }
    // SAFETY: as the caller guarantees.
    unsafe {
        match tasks::group() {
            Some(group) if tasks::reserve() => start(loc, shape, f, group),
            _ => {
                let r = call(loc, f, shape, std::ptr::null_mut());
                if r.raised != 0 {
                    r
                } else {
                    ended(r.value, shape)
                }
            }
        }
    }
}

/// Starts `f` on a thread, as a task of `group`, with a deep copy of what it captures.
///
/// # Safety
///
/// `f` is a live closure of no parameters, which gives a value of the shape `shape`, and only the
/// current thread reaches it, but for what threads share.
unsafe fn start(loc: u64, shape: Shape, f: u64, group: Arc<Group>) -> Ret {
    // SAFETY: as the caller guarantees: the copy reaches nothing the current thread reaches,
    // but what threads share.
    let copied = unsafe { deep_copy(f) };
    let place = tasks::here_or_root().spawn(copied.handles, Some(Arc::clone(&group)));
    if place.closed() {
        // A cut or a cancel closed the code that starts it since its `spawn` began: the
        // sequential run never starts the task.
        // SAFETY: the copy is the current thread's alone.
        unsafe { crate::object::drop(copied.word) };
        place.end();
        return unreached();
    }
    let state = Arc::new(State::default());
    let task = handle(Some(&state)) as u64;
    group.join();
    // A cancel puts the task out of the sequential run: the group waits for it no more
    // (tasks.scope-failure).
    let (detached, out) = (Arc::clone(&state), Arc::clone(&group));
    let waited = tasks::Waited::new(&place, move || {
        finish(&detached, task, None, shape);
        out.leave();
    });
    let (theirs, ours, end, mine, stops) = (
        Arc::clone(&state),
        Arc::clone(&group),
        place.clone(),
        place.clone(),
        waited.clone(),
    );
    let f = copied.word;
    let abandoned = Box::new(move || {
        // SAFETY: the copy is the task's, whose frames, which borrow it, never run again.
        unsafe { crate::object::drop(f) };
        crate::pool::flush();
        if stops.stopped() {
            finish(&theirs, task, None, shape);
            ours.leave();
        }
        end.end();
    });
    let body = Box::new(move || {
        // SAFETY: the copy is the task's alone, and the handle stays alive until `finish` is
        // told that it went.
        unsafe {
            let r = call(loc, f, shape, std::ptr::null_mut());
            crate::object::drop(f);
            let value = (r.raised == 0).then_some(r.value);
            crate::effects::take_unreached(r);
            if waited.ended() {
                finish(&state, task, value, shape);
                crate::pool::flush();
                mine.end();
                group.leave();
                return;
            }
            if let Some(value) = value.filter(|_| shape.heap() || shape.words() > 1) {
                crate::object::drop(value);
            }
        }
        crate::pool::flush();
        mine.end();
    });
    tasks::launch(place, abandoned, body);
    Ret::ok(task)
}

/// Tells those that wait for a task on a thread that it ended, with `value` or without one,
/// which it stores in its handle `task`, or drops if the handle has gone.
pub(crate) fn finish(state: &State, task: u64, value: Option<u64>, shape: Shape) {
    let mut status = state.status.lock().unwrap_or_else(PoisonError::into_inner);
    if let Some(value) = value {
        // SAFETY: the value is the task's alone, and the handle is alive while it isn't
        // orphaned, which its freeing tells under the lock.
        unsafe {
            if status.orphaned {
                if shape.heap() || shape.words() > 1 {
                    crate::object::drop(value);
                }
            } else {
                if status.crossed {
                    share_within(value);
                }
                store(task as *mut Header, value, shape);
            }
        }
    }
    status.ended = Some(value.is_some());
    state.ended.notify_all();
}

/// Shares a task's handle, which another thread reaches from now on, and its value.
///
/// # Safety
///
/// `task` is a live task's handle that only the current thread reaches.
pub(crate) unsafe fn cross(task: *mut Header) {
    // SAFETY: as the caller guarantees; a task on a thread stores its value under the lock.
    unsafe {
        let state = state_of(task);
        let _status = (!state.is_null()).then(|| {
            let mut status = (*state)
                .status
                .lock()
                .unwrap_or_else(PoisonError::into_inner);
            status.crossed = true;
            status
        });
        (*task).flags |= SHARED;
        if data_field_is_heap(task, VALUE) {
            share_within(*data_field(task, VALUE));
        }
    }
}

/// Lets go of the state of a task's handle that goes.
///
/// # Safety
///
/// `task` is a task's handle that nothing references any more.
pub(crate) unsafe fn orphan(task: *mut Header) {
    // SAFETY: as the caller guarantees; the handle owns a reference to its state.
    unsafe {
        let state = state_of(task);
        if state.is_null() {
            return;
        }
        let state = Arc::from_raw(state);
        state
            .status
            .lock()
            .unwrap_or_else(PoisonError::into_inner)
            .orphaned = true;
        *data_field(task, STATE) = 0;
    }
}

/// `t.await()`: the value the task ended with, with references of its own, once it has. A
/// value of several words goes to `out`. A task that ended without a value is one the
/// sequential run never ran, and so is the code that waits for it, which the abort stops.
///
/// # Safety
///
/// `t` is a live task of the shape `shape`, and `out` points to room for the words of a value
/// of several words. The memory for an error, which every call whose row holds `async` is
/// passed, is unused, since an abort raises in one word.
#[unsafe(no_mangle)]
pub(crate) unsafe extern "C" fn stilt_std_task_Task_await(
    _loc: u64,
    shape: u64,
    t: u64,
    out: u64,
    _err: u64,
) -> Ret {
    let out = out as usize as *mut u64;
    let (shape, task) = (Shape(shape), t as *mut Header);
    // SAFETY: as the caller guarantees: the task's value is in its handle once it ended with
    // one, which the lock tells.
    unsafe {
        let state = state_of(task);
        if !state.is_null() {
            let status = (*state)
                .status
                .lock()
                .unwrap_or_else(PoisonError::into_inner);
            let status =
                crate::watch::block(|| (*state).ended.wait_while(status, |s| s.ended.is_none()))
                    .unwrap_or_else(PoisonError::into_inner);
            let ended = status.ended;
            std::mem::drop(status);
            crate::watch::unblock();
            if ended == Some(false) {
                return crate::effects::abort_unreached();
            }
        }
        let value = *data_field(task, VALUE);
        if shape.words() > 1 {
            let words = words_of(&value, shape);
            dup_words(words, shape);
            std::ptr::copy_nonoverlapping(words.as_ptr(), out, words.len());
            return Ret::ok(0);
        }
        if shape.heap() {
            dup(value);
        }
        Ret::ok(value)
    }
}

/// A handler of `async`: the kind of one that resumes at once, and no operation.
fn handler(tag: u16) -> Ret {
    let h = alloc_data(1, tag);
    // SAFETY: the object was just allocated with one field, a scalar.
    unsafe {
        *data_field(h, 0) = 0;
        set_masks(h, |_| 0);
    }
    Ret::ok(h as u64)
}

/// Whether a handler of `async` is `task.threads()`.
///
/// # Safety
///
/// `handler` is a live handler of `async`.
pub(crate) unsafe fn is_threads(handler: u64) -> bool {
    // SAFETY: as the caller guarantees.
    unsafe { (*(handler as *mut Header)).tag == THREADS }
}

/// `task.threads()`.
#[unsafe(no_mangle)]
pub(crate) extern "C" fn stilt_std_task_threads(_loc: u64) -> Ret {
    handler(THREADS)
}

/// `task.sequential()`.
#[unsafe(no_mangle)]
pub(crate) extern "C" fn stilt_std_task_sequential(_loc: u64) -> Ret {
    handler(0)
}

/// The functions of this module that compiled code calls, by name.
pub(crate) fn symbols() -> Vec<(&'static str, *const u8)> {
    crate::exports![
        stilt_std_task_spawn,
        stilt_std_task_Task_await,
        stilt_std_task_threads,
        stilt_std_task_sequential,
    ]
}
