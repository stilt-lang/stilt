//! The options of the sanitizers that `just sanitizers` builds the compiler and its runtime with
//! (goal no-memory-errors), which a program gives by defining `__asan_default_options` and
//! `__tsan_default_options`. Under `AddressSanitizer`, leaks are reported, and segmentation
//! faults are left to the runtime's stack guard, which turns a stack overflow into its report.
//! The guard finds the top of the program's stack from the address of a local, which the fake
//! stacks of the check for uses of a frame after it returns would move, so that check is off.
//! Under `ThreadSanitizer`, the first race ends the run with its report, and the stack guard's
//! handler, which only reports and exits, isn't held to the rules of signal-safe code.

/// The options `AddressSanitizer` takes before those of its environment, which the conformance
/// runner clears.
#[cfg(stilt_sanitizers)]
#[unsafe(no_mangle)]
pub(crate) extern "C" fn __asan_default_options() -> *const std::ffi::c_char {
    c"detect_leaks=1:handle_segv=0:allow_user_segv_handler=1:detect_stack_use_after_return=0"
        .as_ptr()
}

/// The options `ThreadSanitizer` takes before those of its environment.
#[cfg(stilt_tsan)]
#[unsafe(no_mangle)]
pub(crate) extern "C" fn __tsan_default_options() -> *const std::ffi::c_char {
    c"halt_on_error=1:report_signal_unsafe=0".as_ptr()
}

/// Keeps the options in the executable: the sanitizer's reference to them is weak, which
/// takes no code from a library, so the runtime refers to them itself.
pub(crate) fn keep() {
    #[cfg(stilt_sanitizers)]
    std::hint::black_box(__asan_default_options as *const ());
    #[cfg(stilt_tsan)]
    std::hint::black_box(__tsan_default_options as *const ());
}
