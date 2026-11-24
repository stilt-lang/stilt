//! The scopes of `std.task` (tasks.scopes and tasks.scope-failure). In the sequential run, which is
//! the program's meaning under every handler (tasks.sequential-run), `s.spawn` runs its task to its
//! end, so a task that raises raises at `s.spawn`, and the tasks after it never start; the scope
//! ends once its function does, when every task of it has ended. Under `task.threads()` the scope's
//! function runs on a thread, and its tasks on threads of their own (`threaded`), with the same
//! result. A `Scope<E>` is a data object of one field: the state of a scope on threads, or 0.
//!
//! An error of several words goes to the memory that the caller passes after the native's other
//! arguments, which the closures are given in turn (`crate::abi`).

mod threaded;

use std::cell::Cell;

use crate::abi::{Ret, call1, call1_out};
use crate::object::{Header, alloc_data, data_field, drop, set_masks};
use crate::shape::Shape;
use crate::tasks;

thread_local! {
    /// Whether the next `s.spawn` of the current thread raises out of its scope at once, as
    /// compiled code tells it (`stilt_mir`'s `scopes`).
    static DIRECT: Cell<bool> = const { Cell::new(false) };
}

/// The memory for an error of the shape `e` that a native was passed, or null where the error
/// comes back in its word.
fn error_room(e: Shape, err: *mut u64) -> *mut u64 {
    if e.words() > 1 {
        err
    } else {
        std::ptr::null_mut()
    }
}

/// A scope's object, holding `state`.
fn scope_object(state: u64) -> *mut Header {
    let scope = alloc_data(1, 0);
    // SAFETY: the object was just allocated with one field, a scalar.
    unsafe {
        *data_field(scope, 0) = state;
        set_masks(scope, |_| 0);
    }
    scope
}

/// `task.scope(f)`: runs `f` with a new scope, and gives its value, a value of several words
/// written to `out`, or raises what `f` raises, or the first raise of its tasks.
///
/// # Safety
///
/// `f` is a live closure that takes a scope and gives a value of the shape `t`, raising errors
/// of the shape `e`; `out` points to room for a value of several words, and `err` for an error
/// of several words.
#[unsafe(no_mangle)]
pub(crate) unsafe extern "C" fn stilt_std_task_scope(
    loc: u64,
    t: u64,
    e: u64,
    f: u64,
    out: u64,
    err: u64,
) -> Ret {
    let out = out as usize as *mut u64;
    let err = err as usize as *mut u64;
    let (t, e) = (Shape(t), Shape(e));
    if let Some(group) = tasks::group()
        && tasks::reserve()
    {
        // SAFETY: as the caller guarantees.
        return unsafe { threaded::scope(loc, (t, e), f, (out, err), group) };
    }
    let scope = scope_object(0);
    let err = error_room(e, err);
    // SAFETY: as the caller guarantees; `f` borrows the scope, which goes once it ends.
    unsafe {
        let r = if t.words() > 1 {
            call1_out(loc, f, scope as u64, out, err)
        } else {
            call1(loc, f, scope as u64, err)
        };
        drop(scope as u64);
        r
    }
}

/// `s.spawn(f)`: in a scope on threads, when its raise leaves the scope at once, starts `f` on a
/// thread; otherwise runs `f` to its end, and gives the task that ended with its value, or
/// raises what `f` raises, at the call (tasks.scope-failure).
///
/// # Safety
///
/// `scope` is a live scope, and `f` a live closure of no parameters, which gives a value of the
/// shape `u` and raises errors of the shape `e`; `err` points to room for an error of several
/// words.
#[unsafe(no_mangle)]
pub(crate) unsafe extern "C" fn stilt_std_task_Scope_spawn(
    loc: u64,
    e: u64,
    u: u64,
    scope: u64,
    f: u64,
    err: u64,
) -> Ret {
    let err = err as usize as *mut u64;
    let (e, u) = (Shape(e), Shape(u));
    let direct = DIRECT.replace(false);
    if tasks::unreached() {
        return crate::std_task::unreached();
    }
    // SAFETY: as the caller guarantees.
    let state = unsafe { *data_field(scope as *mut Header, 0) };
    if direct && state != 0 && tasks::group().is_some() && tasks::reserve() {
        // SAFETY: as the caller guarantees: a scope's state outlives its function's calls.
        return unsafe { threaded::spawn(loc, (e, u), &*(state as *const threaded::Scope), f) };
    }
    // SAFETY: as the caller guarantees.
    let r = unsafe { crate::std_task::call(loc, f, u, error_room(e, err)) };
    if r.raised != 0 {
        return r;
    }
    crate::std_task::ended(r.value, u)
}

/// Tells the next `s.spawn` of the current thread that its raise leaves its scope at once.
#[unsafe(no_mangle)]
pub(crate) extern "C" fn stilt_rt_scope_direct() {
    DIRECT.set(true);
}

/// The functions of this module that compiled code calls, by name.
pub(crate) fn symbols() -> Vec<(&'static str, *const u8)> {
    crate::exports![
        stilt_std_task_scope,
        stilt_std_task_Scope_spawn,
        stilt_rt_scope_direct
    ]
}
