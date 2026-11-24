//! Stacks of their own on the native targets: each body's context maps a stack, with a guard
//! page below it, and [`switch`] saves the registers that a call preserves on the running stack,
//! and restores those another context saved on its own. A new context starts at an entry
//! function, which never returns: it ends by switching away for the last time. Under the
//! sanitizers, each switch tells `AddressSanitizer` which stack runs next, or `ThreadSanitizer`
//! which fiber.

use std::cell::RefCell;

/// The size of a context's stack, of which only the pages it touches take memory.
const SIZE: usize = 16 * 1024 * 1024;

/// The guard below a stack, which a stack overflow faults on.
const GUARD: usize = 64 * 1024;

/// The stacks kept for the contexts made next, rather than given back.
const KEPT: usize = 16;

/// A stack mapped for a context: its lowest address, guard included.
#[derive(Debug)]
struct Stack(usize);

impl Stack {
    fn new() -> Self {
        if let Some(stack) = FREE.with_borrow_mut(Vec::pop) {
            return stack;
        }
        // SAFETY: an anonymous private mapping of fresh memory has no preconditions, and the
        // guard is the start of that mapping.
        unsafe {
            let base = libc::mmap(
                std::ptr::null_mut(),
                SIZE + GUARD,
                libc::PROT_READ | libc::PROT_WRITE,
                libc::MAP_PRIVATE | libc::MAP_ANON,
                -1,
                0,
            );
            if base == libc::MAP_FAILED {
                crate::panic::panic(0, 0, "no memory left for a handler's stack");
            }
            libc::mprotect(base, GUARD, libc::PROT_NONE);
            Self(base as usize)
        }
    }

    fn top(&self) -> usize {
        self.0 + GUARD + SIZE
    }
}

impl Drop for Stack {
    fn drop(&mut self) {
        // SAFETY: the stack was mapped with this address and size, and no context runs on it.
        unsafe { libc::munmap(self.0 as *mut libc::c_void, SIZE + GUARD) };
    }
}

thread_local! {
    static FREE: RefCell<Vec<Stack>> = const { RefCell::new(Vec::new()) };
}

/// A stack that code runs on, and where its registers are while it doesn't.
#[derive(Debug, Default)]
pub(crate) struct Context {
    sp: usize,
    stack: Option<Stack>,
    /// The lowest address and the size of the stack, as the sanitizers track it.
    #[cfg(stilt_sanitizers)]
    bounds: (usize, usize),
    /// The fiber that `ThreadSanitizer` runs the context's code on.
    #[cfg(stilt_tsan)]
    fiber: super::tsan::Fiber,
}

impl Context {
    /// A context that starts at `entry`, given `arg`, when it is first switched to.
    pub(crate) fn new(entry: super::Entry, arg: usize) -> Self {
        let stack = Stack::new();
        let top = stack.top();
        // SAFETY: the frame lies in the stack just mapped, below its top.
        let sp = unsafe { first_frame(top, entry as usize, arg) };
        Self {
            sp,
            #[cfg(stilt_sanitizers)]
            bounds: (stack.0 + GUARD, SIZE),
            #[cfg(stilt_tsan)]
            fiber: super::tsan::Fiber::new(),
            stack: Some(stack),
        }
    }

    /// Gives back the stack of a context that will never run again. Under the sanitizers, its
    /// shadow is cleared first: a context's entry never returns, so the redzones of its frames
    /// would stay poisoned, and a context that the stack is kept for would meet them.
    pub(crate) fn release(&mut self) {
        if let Some(stack) = self.stack.take() {
            #[cfg(stilt_tsan)]
            self.fiber.release();
            #[cfg(stilt_sanitizers)]
            // SAFETY: the stack is mapped, and no context runs on it any more.
            unsafe {
                sanitizer::__asan_unpoison_memory_region(
                    (stack.0 + GUARD) as *const libc::c_void,
                    SIZE,
                );
            }
            FREE.with_borrow_mut(|free| {
                if free.len() < KEPT {
                    free.push(stack);
                }
            });
        }
    }
}

/// Switches from the running context, `from`, to `to`, and returns once a switch comes back
/// to `from`. `last` tells that `from` never runs again.
///
/// # Safety
///
/// `from` is the running context, and `to` a context that isn't running: one that switched
/// away, or a new one.
pub(crate) unsafe fn switch(from: *mut Context, to: *mut Context, last: bool) {
    // SAFETY: as the caller guarantees.
    unsafe {
        #[cfg(stilt_sanitizers)]
        let mut fake = std::ptr::null_mut();
        #[cfg(stilt_sanitizers)]
        sanitizer::__sanitizer_start_switch_fiber(
            if last {
                std::ptr::null_mut()
            } else {
                &raw mut fake
            },
            (*to).bounds.0 as *const libc::c_void,
            (*to).bounds.1,
        );
        #[cfg(stilt_sanitizers)]
        PREVIOUS.with(|p| p.set(from));
        #[cfg(stilt_tsan)]
        super::tsan::Fiber::switch(&mut (*from).fiber, &(*to).fiber);
        let _ = last;
        swap(&raw mut (*from).sp, (*to).sp);
        #[cfg(stilt_sanitizers)]
        landed(fake);
    }
}

/// Tells the sanitizers that a switch has landed, and records the bounds of the stack it came
/// from, the thread's own among them, which they know first.
///
/// # Safety
///
/// Called once at the end of each switch, on the context it landed on.
#[cfg(stilt_sanitizers)]
unsafe fn landed(fake: *mut libc::c_void) {
    let (mut bottom, mut size) = (std::ptr::null(), 0);
    // SAFETY: called once at the end of a switch, as the sanitizer requires.
    unsafe { sanitizer::__sanitizer_finish_switch_fiber(fake, &raw mut bottom, &raw mut size) };
    PREVIOUS.with(|p| {
        let from = p.get();
        if !from.is_null() {
            // SAFETY: the context that switched here is alive while its switch runs.
            unsafe { (*from).bounds = (bottom as usize, size) };
        }
    });
}

/// Tells the sanitizers that a new context has started.
pub(crate) fn started() {
    #[cfg(stilt_sanitizers)]
    // SAFETY: the context that switched to this one is the thread's or another context.
    unsafe {
        landed(std::ptr::null_mut());
    }
}

#[cfg(stilt_sanitizers)]
thread_local! {
    /// The context being switched from, whose bounds the sanitizer gives once the switch lands.
    static PREVIOUS: std::cell::Cell<*mut Context> = const { std::cell::Cell::new(std::ptr::null_mut()) };
}

#[cfg(stilt_sanitizers)]
mod sanitizer {
    unsafe extern "C" {
        pub(super) fn __sanitizer_start_switch_fiber(
            fake: *mut *mut libc::c_void,
            bottom: *const libc::c_void,
            size: usize,
        );
        pub(super) fn __sanitizer_finish_switch_fiber(
            fake: *mut libc::c_void,
            bottom: *mut *const libc::c_void,
            size: *mut usize,
        );
        pub(super) fn __asan_unpoison_memory_region(start: *const libc::c_void, size: usize);
    }
}

#[cfg(target_arch = "aarch64")]
mod arch {
    /// The bytes a switch saves on the stack it leaves: x19 to x30, then d8 to d15.
    const FRAME: usize = 160;

    /// Writes the frame that a new context's first switch restores, which returns to `start`
    /// with `entry` in x20 and `arg` in x19, and gives its stack pointer.
    ///
    /// # Safety
    ///
    /// `top`, aligned to 16, is the top of a writable stack with room for the frame.
    pub(super) unsafe fn first_frame(top: usize, entry: usize, arg: usize) -> usize {
        let sp = top - FRAME;
        let frame = sp as *mut usize;
        // SAFETY: as the caller guarantees.
        unsafe {
            std::ptr::write_bytes(frame, 0, FRAME / 8);
            frame.write(arg);
            frame.add(1).write(entry);
            frame.add(11).write(start as *const () as usize);
        }
        sp
    }

    /// Where a new context starts: it calls its entry with its argument.
    ///
    /// # Safety
    ///
    /// Only the first switch to a context returns to it, through the frame of [`first_frame`],
    /// whose entry never returns.
    #[unsafe(naked)]
    unsafe extern "C" fn start() {
        std::arch::naked_asm!("mov x0, x19", "blr x20", "brk #1");
    }

    /// Saves the preserved registers on the running stack and its pointer in `*from`, then
    /// restores those saved on the stack `to` points into.
    ///
    /// # Safety
    ///
    /// `from` is where the running context keeps its stack pointer, and `to` the stack pointer
    /// that a context left when it switched away, or that [`first_frame`] gave.
    #[unsafe(naked)]
    pub(super) unsafe extern "C" fn swap(from: *mut usize, to: usize) {
        std::arch::naked_asm!(
            "sub sp, sp, #160",
            "stp x19, x20, [sp, #0]",
            "stp x21, x22, [sp, #16]",
            "stp x23, x24, [sp, #32]",
            "stp x25, x26, [sp, #48]",
            "stp x27, x28, [sp, #64]",
            "stp x29, x30, [sp, #80]",
            "stp d8, d9, [sp, #96]",
            "stp d10, d11, [sp, #112]",
            "stp d12, d13, [sp, #128]",
            "stp d14, d15, [sp, #144]",
            "mov x2, sp",
            "str x2, [x0]",
            "mov sp, x1",
            "ldp x19, x20, [sp, #0]",
            "ldp x21, x22, [sp, #16]",
            "ldp x23, x24, [sp, #32]",
            "ldp x25, x26, [sp, #48]",
            "ldp x27, x28, [sp, #64]",
            "ldp x29, x30, [sp, #80]",
            "ldp d8, d9, [sp, #96]",
            "ldp d10, d11, [sp, #112]",
            "ldp d12, d13, [sp, #128]",
            "ldp d14, d15, [sp, #144]",
            "add sp, sp, #160",
            "ret",
        );
    }
}

#[cfg(target_arch = "x86_64")]
mod arch {
    /// The bytes a switch saves on the stack it leaves: the control words of the floating
    /// point units, r15 to r12, rbx and rbp, then the return address.
    const FRAME: usize = 64;

    /// The control words a thread starts with: MXCSR's in the low half, x87's above.
    const CONTROL: usize = 0x1f80 | 0x037f << 32;

    /// Writes the frame that a new context's first switch restores, which returns to `start`
    /// with `arg` in rbx and `entry` in r12, and gives its stack pointer.
    ///
    /// # Safety
    ///
    /// `top`, aligned to 16, is the top of a writable stack with room for the frame.
    pub(super) unsafe fn first_frame(top: usize, entry: usize, arg: usize) -> usize {
        let sp = top - FRAME;
        let frame = sp as *mut usize;
        // SAFETY: as the caller guarantees.
        unsafe {
            std::ptr::write_bytes(frame, 0, FRAME / 8);
            frame.write(CONTROL);
            frame.add(4).write(entry);
            frame.add(5).write(arg);
            frame.add(7).write(start as *const () as usize);
        }
        sp
    }

    /// Where a new context starts: it calls its entry with its argument.
    ///
    /// # Safety
    ///
    /// Only the first switch to a context returns to it, through the frame of [`first_frame`],
    /// whose entry never returns.
    #[unsafe(naked)]
    unsafe extern "C" fn start() {
        std::arch::naked_asm!("mov rdi, rbx", "call r12", "ud2");
    }

    /// Saves the preserved registers on the running stack and its pointer in `*from`, then
    /// restores those saved on the stack `to` points into.
    ///
    /// # Safety
    ///
    /// `from` is where the running context keeps its stack pointer, and `to` the stack pointer
    /// that a context left when it switched away, or that [`first_frame`] gave.
    #[unsafe(naked)]
    pub(super) unsafe extern "C" fn swap(from: *mut usize, to: usize) {
        std::arch::naked_asm!(
            "push rbp",
            "push rbx",
            "push r12",
            "push r13",
            "push r14",
            "push r15",
            "sub rsp, 8",
            "stmxcsr [rsp]",
            "fnstcw [rsp + 4]",
            "mov [rdi], rsp",
            "mov rsp, rsi",
            "ldmxcsr [rsp]",
            "fldcw [rsp + 4]",
            "add rsp, 8",
            "pop r15",
            "pop r14",
            "pop r13",
            "pop r12",
            "pop rbx",
            "pop rbp",
            "ret",
        );
    }
}

use arch::{first_frame, swap};
