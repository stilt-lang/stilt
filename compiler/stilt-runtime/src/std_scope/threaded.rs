//! Scopes under `task.threads()` (tasks.scope-failure). The scope's function runs on a thread, in a
//! segment of its own (`crate::tasks`), with a deep copy of what it captures, as a task's
//! function has, while the code that called `task.scope` waits for it.
//! A task that it starts by an `s.spawn` whose raise leaves the scope at once runs on a thread
//! of its own while the function goes on, as the sequential run goes on when the task doesn't
//! raise. When such a task raises, unless a raise before it in the sequential order already
//! cancelled it, the function's segment is cut after the task's: the tasks after it are
//! cancelled, and nothing they or the function write from then on appears, and its error is
//! the scope's first raise so far, every later one having been cut. Code past that raise stops
//! when it waits for a task that ended without a value, by the abort of `crate::std_task`'s
//! `await`, or for good at a point it can't take back (`crate::tasks`).
//!
//! The scope ends once its function and every task of it that the sequential run reaches have
//! ended or stopped, with the first raise if there is one, and otherwise with the function's
//! value or raise. It waits for nothing that a cut or a cancel put out of the sequential run
//! (`crate::tasks::Waited`), which goes on unseen on its thread, holding the scope's object.

use std::sync::{Arc, Condvar, Mutex, MutexGuard, PoisonError};

use super::{error_room, scope_object};
use crate::abi::{Ret, call1, call1_out};
use crate::map::drop_words;
use crate::object::{deep_copy, drop};
use crate::shape::Shape;
use crate::std_task::{State, call, finish, handle};
use crate::tasks::{self, Group, Here, Waited};

/// How the scope's function ended: with its value's words, its error's, or stopped.
#[derive(Debug)]
enum Ending {
    Value(Vec<u64>),
    Raised(Vec<u64>),
    Stopped,
}

#[derive(Debug, Default)]
struct Inner {
    /// The first raise in the sequential order so far: its error's words.
    first: Option<Vec<u64>>,
    /// The function and the tasks that haven't ended or stopped.
    live: usize,
    ended: Option<Ending>,
}

/// A scope on threads.
#[derive(Debug)]
pub(crate) struct Scope {
    inner: Mutex<Inner>,
    changed: Condvar,
    /// The segment of its function.
    place: Here,
    /// The shapes of its value and its error.
    t: Shape,
    e: Shape,
}

impl Scope {
    fn inner(&self) -> MutexGuard<'_, Inner> {
        self.inner.lock().unwrap_or_else(PoisonError::into_inner)
    }

    fn leave(&self) {
        self.inner().live -= 1;
        self.changed.notify_all();
    }

    /// The words of an error that a call raised, as `r` and the memory `err` give it.
    fn error(&self, r: Ret, err: &[u64]) -> Vec<u64> {
        if self.e.words() > 1 {
            err.to_vec()
        } else {
            vec![r.value]
        }
    }

    /// A task of the scope, in the segment `at`, raised `error`.
    fn raised(&self, at: &Here, error: Vec<u64>) {
        let run = &self.place.run;
        let mut tree = run.lock();
        if tree.closed(at.seg) {
            // SAFETY: the error is the task's alone, and owns its references.
            unsafe { drop_words(&error, self.e) };
            return;
        }
        tree.cut(self.place.seg, at.seg);
        let mut inner = self.inner();
        if let Some(cut) = inner.first.replace(error) {
            // SAFETY: as above, for the raise this one cut.
            unsafe { drop_words(&cut, self.e) };
        }
        std::mem::drop((inner, tree));
        run.changed();
    }
}

/// `task.scope(f)` on threads, its value of the shape `t` going to `out` and its error of the
/// shape `e` to `err` when they have several words.
///
/// # Safety
///
/// As for `task.scope`, and a job may start on a thread (`crate::tasks::reserve`).
pub(super) unsafe fn scope(
    loc: u64,
    (t, e): (Shape, Shape),
    f: u64,
    (out, err): (*mut u64, *mut u64),
    group: Arc<Group>,
) -> Ret {
    // SAFETY: as the caller guarantees: the copy reaches nothing the current thread reaches,
    // but what threads share, so a function that a cut leaves running past the scope's end
    // reaches nothing that the caller lets go of.
    let f = unsafe { deep_copy(f) }.word;
    let place = tasks::here_or_root().spawn(true, Some(group));
    let scope = Arc::new(Scope {
        inner: Mutex::new(Inner {
            live: 1,
            ..Inner::default()
        }),
        changed: Condvar::new(),
        place: place.clone(),
        t,
        e,
    });
    // The object is the function's thread's alone, which lets go of it once the function ends or
    // stops for good: a cut may leave it running past the scope's end.
    let object = scope_object(Arc::as_ptr(&scope) as u64) as u64;
    let cut = Arc::clone(&scope);
    let waited = Waited::new(&place, move || {
        cut.inner().ended = Some(Ending::Stopped);
        cut.leave();
    });
    let (theirs, ours, stops) = (Arc::clone(&scope), Arc::clone(&scope), waited.clone());
    let abandoned = Box::new(move || {
        // SAFETY: the function's frames, which borrow the object and the copy, never run again.
        unsafe {
            drop(object);
            drop(f);
        }
        crate::pool::flush();
        if stops.stopped() {
            theirs.inner().ended = Some(Ending::Stopped);
            theirs.leave();
        }
        theirs.place.end();
    });
    let body = Box::new(move || {
        // SAFETY: the caller of `task.scope` waits until the function ends, unless a cut put it
        // out of the sequential run, so the function's thread alone reaches what it holds.
        unsafe {
            let ending = function(loc, f, object, &ours);
            drop(object);
            drop(f);
            if waited.ended() {
                ours.inner().ended = Some(ending);
                crate::pool::flush();
                ours.place.end();
                ours.leave();
                return;
            }
            forget(ending, (ours.t, ours.e));
        }
        crate::pool::flush();
        ours.place.end();
    });
    tasks::launch(place, abandoned, body);
    let inner = scope.inner();
    let mut inner = crate::watch::block(|| scope.changed.wait_while(inner, |i| i.live > 0))
        .unwrap_or_else(PoisonError::into_inner);
    let (first, ended) = (inner.first.take(), inner.ended.take());
    std::mem::drop(inner);
    crate::watch::unblock();
    // SAFETY: the words are the scope's, which own their references, and the caller of
    // `task.scope` gave room for them.
    unsafe { result((first, ended), (t, e), (out, err)) }
}

/// Lets go of what a function that a cut put out of the sequential run ended with.
///
/// # Safety
///
/// The words own their references.
unsafe fn forget(ending: Ending, (t, e): (Shape, Shape)) {
    // SAFETY: as the caller guarantees.
    unsafe {
        match ending {
            Ending::Value(v) => drop_words(&v[..t.words().max(1)], t),
            Ending::Raised(x) => drop_words(&x, e),
            Ending::Stopped => {}
        }
    }
}

/// Runs the scope's function on the scope's object, and tells how it ended.
///
/// # Safety
///
/// `f` is a live closure of one parameter, which gives a value of the shape `scope.t` and raises
/// an error of the shape `scope.e`, and `object` a word of its parameter's type.
unsafe fn function(loc: u64, f: u64, object: u64, scope: &Scope) -> Ending {
    let mut words = vec![0u64; scope.t.words().max(1)];
    let mut err = vec![0u64; scope.e.words().max(1)];
    let room = error_room(scope.e, err.as_mut_ptr());
    // SAFETY: as the caller guarantees.
    let r = unsafe {
        if scope.t.words() > 1 {
            call1_out(loc, f, object, words.as_mut_ptr(), room)
        } else {
            call1(loc, f, object, room)
        }
    };
    if r.raised == 0 {
        if scope.t.words() <= 1 {
            words[0] = r.value;
        }
        Ending::Value(words)
    } else if crate::effects::take_unreached(r) {
        Ending::Stopped
    } else {
        err.truncate(scope.e.words());
        Ending::Raised(scope.error(r, &err))
    }
}

/// The scope's result: its first raise, or its function's value or raise.
///
/// # Safety
///
/// The words own their references, and `out` and `err` have room for a value and an error of
/// several words.
unsafe fn result(
    (first, ended): (Option<Vec<u64>>, Option<Ending>),
    (t, e): (Shape, Shape),
    (out, err): (*mut u64, *mut u64),
) -> Ret {
    let give = |words: &[u64], to: *mut u64, raise: bool| {
        if words.len() > 1 {
            // SAFETY: as the caller guarantees.
            unsafe { std::ptr::copy_nonoverlapping(words.as_ptr(), to, words.len()) };
        }
        let word = if words.len() > 1 { 0 } else { words[0] };
        if raise {
            Ret::raise(word)
        } else {
            Ret::ok(word)
        }
    };
    match (first, ended) {
        (Some(error), ended) => {
            // SAFETY: as the caller guarantees; the cut function's value or raise goes.
            unsafe { forget(ended.unwrap_or(Ending::Stopped), (t, e)) };
            give(&error, err, true)
        }
        (None, Some(Ending::Value(v))) => give(&v, out, false),
        (None, Some(Ending::Raised(x))) => give(&x, err, true),
        // The function stopped as code the sequential run never reaches, and so is the code
        // that called it.
        (None, _) => crate::effects::abort_unreached(),
    }
}

/// `s.spawn(f)` in a scope on threads, whose raise leaves the scope at once: starts `f` on a
/// thread, with a deep copy of what it captures, as a task of the scope.
///
/// # Safety
///
/// As for `s.spawn`, and a job may start on a thread (`crate::tasks::reserve`).
pub(super) unsafe fn spawn(loc: u64, (e, u): (Shape, Shape), scope: &Scope, f: u64) -> Ret {
    // SAFETY: as the caller guarantees: the copy reaches nothing the current thread reaches,
    // but what threads share.
    let copied = unsafe { deep_copy(f) };
    let here = tasks::here().expect("a scope's function runs in a segment");
    let place = here.spawn(true, here.group.clone());
    if closed(&place, copied.word) {
        return crate::std_task::unreached();
    }
    let state = Arc::new(State::default());
    let task = handle(Some(&state)) as u64;
    scope.inner().live += 1;
    let scope = scope_arc(scope);
    let waited = waited(&place, &state, task, &scope, u);
    let (theirs, ours, at, stops) = (
        Arc::clone(&state),
        Arc::clone(&scope),
        place.clone(),
        waited.clone(),
    );
    let f = copied.word;
    let abandoned = Box::new(move || {
        // SAFETY: the copy is the task's, whose frames, which borrow it, never run again.
        unsafe { drop(f) };
        crate::pool::flush();
        if stops.stopped() {
            finish(&theirs, task, None, u);
            ours.leave();
        }
        at.end();
    });
    let at = place.clone();
    let body = Box::new(move || {
        let mut err = vec![0u64; e.words().max(1)];
        // SAFETY: the copy is the task's alone, and the handle stays alive until `finish` is
        // told that it went.
        unsafe {
            let r = call(loc, f, u, error_room(e, err.as_mut_ptr()));
            drop(f);
            let raised = r.raised != 0 && !crate::effects::take_unreached(r);
            if !waited.ended() {
                let error = raised.then(|| &err[..e.words().max(1)]);
                forget_task(r, error, &scope, u);
                crate::pool::flush();
                at.end();
                return;
            }
            if r.raised == 0 {
                finish(&state, task, Some(r.value), u);
            } else {
                if raised {
                    err.truncate(e.words());
                    scope.raised(&at, scope.error(r, &err));
                }
                finish(&state, task, None, u);
            }
        }
        crate::pool::flush();
        at.end();
        scope.leave();
    });
    tasks::launch(place, abandoned, body);
    Ret::ok(task)
}

/// Waits for a task of the scope, of the handle `task`, until a cancel puts it out of the
/// sequential run, when the scope waits for it no more.
fn waited(place: &Here, state: &Arc<State>, task: u64, scope: &Arc<Scope>, u: Shape) -> Waited {
    let (detached, out) = (Arc::clone(state), Arc::clone(scope));
    Waited::new(place, move || {
        finish(&detached, task, None, u);
        out.leave();
    })
}

/// Whether a raise before it cut the function since its `s.spawn` began, so that the sequential
/// run never starts the task: the task's segment and its copy `f` then go.
fn closed(place: &Here, f: u64) -> bool {
    if !place.closed() {
        return false;
    }
    // SAFETY: the copy is the current thread's alone.
    unsafe { drop(f) };
    place.end();
    true
}

/// Lets go of what a task that a cancel put out of the sequential run ended with: its value of
/// the shape `u`, or its error, which `error` holds when it has several words.
///
/// # Safety
///
/// The value or the error owns its references.
unsafe fn forget_task(r: Ret, error: Option<&[u64]>, scope: &Scope, u: Shape) {
    // SAFETY: as the caller guarantees.
    unsafe {
        match error {
            None if r.raised == 0 && (u.heap() || u.words() > 1) => drop(r.value),
            None => {}
            Some(err) => drop_words(&scope.error(r, err), scope.e),
        }
    }
}

/// The scope that `scope` points into, counted once more.
fn scope_arc(scope: &Scope) -> Arc<Scope> {
    let at: *const Scope = scope;
    // SAFETY: every scope on threads is in an `Arc`, which its `task.scope` holds until each of
    // its tasks has ended or stopped.
    unsafe {
        Arc::increment_strong_count(at);
        Arc::from_raw(at)
    }
}
