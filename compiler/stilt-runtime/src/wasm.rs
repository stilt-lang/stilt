//! What the runtime does otherwise on WebAssembly, a WASI preview 1 command that runs on one
//! thread with no signals (wasm.tasks-in-order and wasm.limits).
//!
//! The module's C stack, below `__stack_pointer`, lies first in memory, so that running past
//! its end traps, and each function of compiled code checks at its entry that the stack pointer
//! is above [`stilt_rt_stack_limit`], which lies [`MARGIN`] above the end of the stack that
//! runs, so that the report of an overflow has room. A stack overflow and running out of memory
//! end the program with status 134, which WASI's `proc_exit` can't give, since it takes a
//! status only below 126, and the runtime traps instead, which ends a module with 134
//! ([`end`]). The stack pointer is a global of the module that only WebAssembly's own
//! instructions reach, which the C of a build defines functions of (`stilt-codegen-c`'s
//! `assemble`).

use std::sync::atomic::{AtomicUsize, Ordering};

/// The room below the end that a function checks, for the runtime's own frames, which check
/// nothing, and the report of an overflow.
pub(crate) const MARGIN: usize = 128 * 1024;

/// The lowest address that the stack pointer of the running stack may hold at a function's
/// entry. A function finding it lower ends the program ([`stilt_rt_stack_overflow`]).
#[unsafe(no_mangle)]
pub(crate) static stilt_rt_stack_limit: AtomicUsize = AtomicUsize::new(0);

unsafe extern "C" {
    /// The lowest address of the module's own stack, which the linker places first in memory.
    static __stack_low: u8;
    fn stilt_rt_stack_pointer() -> usize;
    fn stilt_rt_set_stack_pointer(sp: usize);
}

/// Readies the module's own stack, whose functions check against its end from here on.
pub(crate) fn prepare() {
    let low = (&raw const __stack_low) as usize;
    stilt_rt_stack_limit.store(low + MARGIN, Ordering::Relaxed);
}

/// The stack pointer of the running stack.
pub(crate) fn stack_pointer() -> usize {
    // SAFETY: the function reads a global.
    unsafe { stilt_rt_stack_pointer() }
}

/// The end that functions check the running stack against.
pub(crate) fn limit() -> usize {
    stilt_rt_stack_limit.load(Ordering::Relaxed)
}

/// Makes the stack at `sp`, whose functions check against `limit`, the running one.
///
/// # Safety
///
/// `sp` is the pointer of a stack that nothing else uses, aligned to 16, above `limit`, and
/// no frame below the caller's will be popped onto the stack it leaves.
pub(crate) unsafe fn set_stack(sp: usize, limit: usize) {
    stilt_rt_stack_limit.store(limit, Ordering::Relaxed);
    // SAFETY: as the caller guarantees.
    unsafe { stilt_rt_set_stack_pointer(sp) };
}

/// Ends the program because a function found the stack past its end (program.exit-statuses). The
/// running stack is then the margin below the end, which the report fits in.
#[unsafe(no_mangle)]
pub(crate) extern "C" fn stilt_rt_stack_overflow() -> ! {
    crate::entry::fatal("stack overflow")
}

/// Ends the module with `status`: 134, which `proc_exit` can't give, by a trap, which the
/// runtime that runs the module ends with 134 (wasm.exit-statuses), and any other by
/// `proc_exit`.
pub(crate) fn end(status: i32) -> ! {
    if status == 134 {
        core::arch::wasm32::unreachable()
    }
    std::process::exit(status)
}

/// Whether a read of standard input would return at once: something is waiting, or the input
/// has ended or can't be read, which ends it. WASI polls a descriptor through `poll_oneoff`,
/// which wasi-libc's `poll` calls.
pub(crate) fn stdin_readable() -> bool {
    let mut fd = libc::pollfd {
        fd: 0,
        events: libc::POLLIN,
        revents: 0,
    };
    // SAFETY: `fd` is one descriptor's entry, which lives across the call.
    unsafe { libc::poll(&raw mut fd, 1, 0) != 0 }
}

/// Fills `bytes` from WASI's `random_get`, which wasi-libc's `getentropy` calls, and tells
/// whether it could.
pub(crate) fn entropy(bytes: &mut [u8]) -> bool {
    // SAFETY: `bytes` is writable for its length, which is below `getentropy`'s 256.
    unsafe { libc::getentropy(bytes.as_mut_ptr().cast(), bytes.len()) == 0 }
}

/// Whether `path` lies in a directory that the runtime granted the module, which wasi-libc
/// resolves it against: a path outside them raises `PermissionDenied` (wasm.what-std-reads), where
/// the system finds nothing at it.
pub(crate) fn granted(path: &str) -> bool {
    let Ok(name) = std::ffi::CString::new(path) else {
        return false;
    };
    let mut room = vec![0u8; 256];
    loop {
        let mut prefix = std::ptr::null();
        let mut relative = room.as_mut_ptr().cast();
        // SAFETY: the name is a C string, and `relative` points to `room`, of the length given.
        let fd = unsafe {
            libc::__wasilibc_find_relpath(
                name.as_ptr(),
                &raw mut prefix,
                &raw mut relative,
                room.len(),
            )
        };
        // The relative path didn't fit in the room, which then grows.
        if fd == -1 && std::io::Error::last_os_error().raw_os_error() == Some(libc::ENOMEM) {
            room.resize(2 * room.len(), 0);
            continue;
        }
        return fd != -1;
    }
}
