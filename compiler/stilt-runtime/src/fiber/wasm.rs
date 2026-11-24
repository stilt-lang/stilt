//! Stacks of their own on WebAssembly (wasm.handlers-that-resume), whose code can't reach the
//! engine's stack: a body runs on that stack above the context that switches to it, and when
//! it switches back its frames are taken off, by binaryen's Asyncify, which saves each frame's
//! locals in the body's memory as the frames return, and puts them back as a later switch to
//! the body calls its entry again. So a switch to a body starts or rewinds it on top of the
//! running context ([`enter`]), and a switch back unwinds it to that switch ([`leave`]): a
//! body only ever switches to the context below it, the one that ran it, as `crate::effects`
//! switches. The frames that C code addresses, below `__stack_pointer`, lie in a region of the
//! body's own memory, whose end the functions of compiled code check at entry
//! (`crate::wasm`).
//!
//! Asyncify instruments only the functions that are on a body's frames when it switches back:
//! the body's entry, `resume`, the switch and the compiled bodies of handlers that call
//! `resume`, which the build lists by these names. The runtime that starts, ends, rewinds and
//! unwinds, [`enter`] and [`leave`], isn't instrumented, as Asyncify requires.

use std::cell::{Cell, RefCell};

use super::Entry;

/// The size of the C stack of a body, past the room of [`crate::wasm::MARGIN`] below it.
const STACK: usize = 1024 * 1024;

/// The room for the locals that Asyncify saves of a body's frames: a handful of frames, since
/// a body switches back only in `resume`, which it calls itself (handlers.resuming).
const SAVED: usize = 64 * 1024;

/// The size of a body's memory: the room for its saved locals, then its stack.
const SIZE: usize = SAVED + crate::wasm::MARGIN + STACK;

/// The memory kept for the bodies made next, rather than given back.
const KEPT: usize = 16;

/// Where Asyncify keeps the locals it saves: the next free byte and the end of the room, as its
/// pass reads them.
#[repr(C)]
#[derive(Debug, Default)]
struct Saved {
    next: usize,
    end: usize,
}

/// The memory of a body, aligned to 16 as a stack must be.
#[derive(Debug)]
struct Memory(*mut u8);

impl Memory {
    fn layout() -> std::alloc::Layout {
        std::alloc::Layout::from_size_align(SIZE, 16).unwrap_or_else(|_| std::process::abort())
    }

    fn new() -> Self {
        if let Some(memory) = FREE.with_borrow_mut(Vec::pop) {
            return memory;
        }
        // SAFETY: the layout has a nonzero size.
        let base = unsafe { std::alloc::alloc(Self::layout()) };
        if base.is_null() {
            crate::entry::fatal("out of memory");
        }
        Self(base)
    }

    fn base(&self) -> usize {
        self.0 as usize
    }
}

impl Drop for Memory {
    fn drop(&mut self) {
        // SAFETY: the memory was allocated with this layout, and no body runs on it.
        unsafe { std::alloc::dealloc(self.0, Self::layout()) };
    }
}

thread_local! {
    static FREE: RefCell<Vec<Memory>> = const { RefCell::new(Vec::new()) };
    /// Set while a switch rewinds a body, until its frames reach the switch it left by.
    static REWINDING: Cell<bool> = const { Cell::new(false) };
    /// Set while a body's frames unwind, until they reach the switch that ran it.
    static UNWINDING: Cell<bool> = const { Cell::new(false) };
}

#[link(wasm_import_module = "asyncify")]
unsafe extern "C" {
    #[link_name = "start_unwind"]
    fn start_unwind(saved: *mut Saved);
    #[link_name = "stop_unwind"]
    fn stop_unwind();
    #[link_name = "start_rewind"]
    fn start_rewind(saved: *mut Saved);
    #[link_name = "stop_rewind"]
    fn stop_rewind();
}

/// Where a context is.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
enum State {
    /// On the engine's stack: running, or below the running context. The thread's own context
    /// is always there.
    #[default]
    Placed,
    /// A body not yet started.
    Fresh,
    /// A body whose frames were unwound into its memory.
    Unwound,
}

/// A stack that code runs on, and for a body, its entry and memory.
#[derive(Debug, Default)]
pub(crate) struct Context {
    state: State,
    /// The C stack's pointer, and the end its functions check, while the context doesn't run.
    sp: usize,
    limit: usize,
    saved: Saved,
    entry: Option<(Entry, usize)>,
    memory: Option<Memory>,
}

impl Context {
    /// A context that starts at `entry`, given `arg`, when it is first switched to.
    pub(crate) fn new(entry: Entry, arg: usize) -> Self {
        let memory = Memory::new();
        let base = memory.base();
        Self {
            state: State::Fresh,
            sp: base + SIZE,
            limit: base + SAVED + crate::wasm::MARGIN,
            saved: Saved::default(),
            entry: Some((entry, arg)),
            memory: Some(memory),
        }
    }

    /// Gives back the memory of a context that will never run again.
    pub(crate) fn release(&mut self) {
        if let Some(memory) = self.memory.take() {
            FREE.with_borrow_mut(|free| {
                if free.len() < KEPT {
                    free.push(memory);
                }
            });
        }
    }
}

/// Switches from the running context, `from`, to `to`, and returns once a switch comes back to
/// `from`, or, when `last` tells that `from` never runs again, at once, for its entry to
/// return. A switch to a body that isn't placed starts or rewinds it; any other goes back to
/// the context below.
///
/// # Safety
///
/// `from` is the running context, and `to` a body that switched away or a new one, or the
/// context below `from`, which ran it.
#[inline(never)]
#[unsafe(export_name = "stilt_rt_fiber_switch")]
pub(crate) unsafe fn switch(from: *mut Context, to: *mut Context, last: bool) {
    // SAFETY: as the caller guarantees.
    unsafe {
        if (*to).state == State::Placed {
            leave(from, last);
        } else {
            enter(from, to);
        }
    }
}

/// Runs the body `to` on top of `from` until it switches back: starts it, or rewinds its frames
/// from its memory, on its own C stack.
///
/// # Safety
///
/// As for [`switch`], with `to` a body that isn't placed.
#[inline(never)]
#[unsafe(export_name = "stilt_rt_fiber_enter")]
unsafe extern "C" fn enter(from: *mut Context, to: *mut Context) {
    // SAFETY: as the caller guarantees: `to` was made by `Context::new`, so it has an entry,
    // and its C stack lies in its memory.
    unsafe {
        (*from).sp = crate::wasm::stack_pointer();
        (*from).limit = crate::wasm::limit();
        crate::wasm::set_stack((*to).sp, (*to).limit);
        if (*to).state == State::Unwound {
            REWINDING.set(true);
            start_rewind(&raw mut (*to).saved);
        }
        (*to).state = State::Placed;
        let Some((entry, arg)) = (*to).entry else {
            std::process::abort()
        };
        entry(arg);
        if UNWINDING.replace(false) {
            stop_unwind();
            (*to).state = State::Unwound;
        }
        crate::wasm::set_stack((*from).sp, (*from).limit);
    }
}

/// Switches from the running body `from` back to the context below it, which ran it: unwinds
/// its frames into its memory, or, when a switch rewinds them, ends the rewinding, which
/// resumes the body where it left. A last switch does neither, and the body's entry returns.
///
/// # Safety
///
/// `from` is the running context, a body that a switch started or rewound.
#[inline(never)]
#[unsafe(export_name = "stilt_rt_fiber_leave")]
unsafe extern "C" fn leave(from: *mut Context, last: bool) {
    if REWINDING.replace(false) {
        // SAFETY: a switch to this body started the rewinding.
        unsafe { stop_rewind() };
        return;
    }
    if last {
        return;
    }
    // SAFETY: as the caller guarantees: the room for the saved locals starts the body's memory.
    unsafe {
        let base = (*from).memory.as_ref().map_or(0, Memory::base);
        (*from).saved = Saved {
            next: base,
            end: base + SAVED,
        };
        (*from).sp = crate::wasm::stack_pointer();
        UNWINDING.set(true);
        start_unwind(&raw mut (*from).saved);
    }
}

/// Tells the sanitizers that a new context has started, which they don't watch here.
pub(crate) fn started() {}
