//! What a switch tells `ThreadSanitizer`, under `just sanitizers` with `STILT_SANITIZER=thread`
//! (goal no-memory-errors): each context runs on a fiber of its own, made with it and destroyed
//! when its stack is given back, and a switch tells the sanitizer which fiber runs next, so that
//! it orders the accesses of each stack as the switches do rather than taking two stacks of one
//! thread for two threads.

/// A context's fiber, as the sanitizer names it: none yet for a thread's own context, whose
/// fiber the sanitizer made with the thread, and which a first switch away from it names.
#[derive(Debug, Default)]
pub(super) struct Fiber(usize);

impl Fiber {
    /// A fiber for a new context.
    pub(super) fn new() -> Self {
        // SAFETY: making a fiber has no preconditions; 0 asks for no flags.
        Self(unsafe { __tsan_create_fiber(0) } as usize)
    }

    /// Tells the sanitizer that `to`'s fiber runs next, after naming `from`'s, the running one.
    ///
    /// # Safety
    ///
    /// `from` is the running context's fiber, and `to` a fiber that isn't running.
    pub(super) unsafe fn switch(from: &mut Fiber, to: &Fiber) {
        // SAFETY: as the caller guarantees; 0 asks the switch to order the two fibers' accesses.
        unsafe {
            if from.0 == 0 {
                from.0 = __tsan_get_current_fiber() as usize;
            }
            __tsan_switch_to_fiber(to.0 as *mut libc::c_void, 0);
        }
    }

    /// Destroys the fiber of a context that never runs again.
    pub(super) fn release(&mut self) {
        if self.0 != 0 {
            // SAFETY: the fiber was made by `new`, and no context runs on it any more.
            unsafe { __tsan_destroy_fiber(self.0 as *mut libc::c_void) };
            self.0 = 0;
        }
    }
}

unsafe extern "C" {
    fn __tsan_create_fiber(flags: u32) -> *mut libc::c_void;
    fn __tsan_destroy_fiber(fiber: *mut libc::c_void);
    fn __tsan_get_current_fiber() -> *mut libc::c_void;
    fn __tsan_switch_to_fiber(fiber: *mut libc::c_void, flags: u32);
}
