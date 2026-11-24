//! The pool that compiled code reaches without a call, which the thread that runs a program's
//! entry owns, and the pools of the other threads, which only the runtime reaches.

use std::sync::atomic::Ordering;

use super::{KEEPS, Pool};

/// The pool that compiled code reaches, which only the thread that owns it uses.
#[repr(transparent)]
pub(crate) struct Owned(pub(super) Pool);

// SAFETY: only the thread whose pointer is the pool's owner reads or writes its cells, and a
// thread pointer is unique among the threads that run; its owner is atomic. A thread takes the
// pool with an `Acquire` exchange from 0 ([`own`]) and gives it up with a `Release` exchange to 0
// ([`give_up`]), so every write of one owner to the cells happens before every access of the next.
// The loads that compare the owner with the current thread's pointer may be `Relaxed`: a thread
// finds its own pointer there only after its own exchange wrote it, which its program order
// already places before the load, and any other value sends it to its own pool.
unsafe impl Sync for Owned {}

/// The pool of the thread that runs a program's entry, `stilt_rt_pool` to compiled code.
#[unsafe(export_name = "stilt_rt_pool")]
pub(crate) static POOL: Owned = Owned(Pool::new());

thread_local! {
    static MEMORY: Pool = const { Pool::new() };
}

/// The current thread's pointer, unique among the threads that run, as compiled code reads it
/// (`stilt-codegen-c`'s `stilt.h`): never 0, and 1 on a target of one thread.
#[inline]
fn thread_pointer() -> usize {
    let pointer: usize;
    #[cfg(all(target_arch = "aarch64", target_vendor = "apple", not(miri)))]
    // SAFETY: reading the thread's register touches no memory. The low bits may hold the
    // processor's number, which changes as the thread moves.
    unsafe {
        std::arch::asm!(
            "mrs {}, tpidrro_el0",
            out(reg) pointer,
            options(nomem, nostack, preserves_flags)
        );
    }
    #[cfg(all(target_arch = "aarch64", not(target_vendor = "apple"), not(miri)))]
    // SAFETY: as above.
    unsafe {
        std::arch::asm!(
            "mrs {}, tpidr_el0",
            out(reg) pointer,
            options(nomem, nostack, preserves_flags)
        );
    }
    #[cfg(all(target_arch = "x86_64", target_os = "linux", not(miri)))]
    // SAFETY: the first word of a thread's control block points to itself.
    unsafe {
        std::arch::asm!(
            "mov {}, qword ptr fs:0",
            out(reg) pointer,
            options(nostack, preserves_flags, readonly)
        );
    }
    #[cfg(target_family = "wasm")]
    {
        pointer = 1;
    }
    // Miri runs no assembly; a thread-local's address is as unique to the thread.
    #[cfg(any(
        miri,
        not(any(
            target_arch = "aarch64",
            all(target_arch = "x86_64", target_os = "linux"),
            target_family = "wasm"
        ))
    ))]
    {
        thread_local! { static HERE: u8 = const { 0 }; }
        pointer = HERE.with(|here| std::ptr::from_ref(here) as usize);
    }
    if cfg!(target_family = "wasm") {
        pointer
    } else {
        pointer & !7
    }
}

/// Runs `f` with the current thread's pool.
#[inline]
pub(crate) fn with<R>(f: impl FnOnce(&Pool) -> R) -> R {
    if POOL.0.owner.load(Ordering::Relaxed) == thread_pointer() {
        // SAFETY: `in_register` gives back the address it is given.
        return f(unsafe { &*in_register(&raw const POOL.0) });
    }
    with_local(f)
}

/// The address `p`, which the compiler then holds in a register and reaches each field through,
/// rather than forming the static's address again for each, which takes two instructions.
#[inline]
fn in_register(p: *const Pool) -> *const Pool {
    #[cfg(not(target_family = "wasm"))]
    {
        let mut address = p as usize;
        // SAFETY: an empty instruction reads and writes nothing but the register.
        unsafe {
            std::arch::asm!(
                "/* {0} */",
                inout(reg) address,
                options(pure, nomem, nostack, preserves_flags)
            );
        }
        p.with_addr(address)
    }
    #[cfg(target_family = "wasm")]
    p
}

/// Runs `f` with the pool of a thread that doesn't own [`POOL`], apart, so that the compiler
/// can't look its thread-local variable up, a call on macOS, before it knows it needs it.
#[cold]
#[inline(never)]
fn with_local<R>(f: impl FnOnce(&Pool) -> R) -> R {
    MEMORY.with(f)
}

/// Makes the current thread the owner of [`POOL`], unless another thread owns it: the thread
/// that runs a program's entry, before it runs.
pub(crate) fn own() {
    if KEEPS {
        let _ = POOL.0.owner.compare_exchange(
            0,
            thread_pointer(),
            Ordering::Acquire,
            Ordering::Relaxed,
        );
    }
}

/// [`POOL`], if the current thread owns it.
#[inline]
pub(super) fn owned() -> Option<&'static Pool> {
    // SAFETY: `in_register` gives back the address it is given.
    (POOL.0.owner.load(Ordering::Relaxed) == thread_pointer())
        .then(|| unsafe { &*in_register(&raw const POOL.0) })
}

/// Gives up [`POOL`] if the current thread owns it.
pub(super) fn give_up() {
    let _ =
        POOL.0
            .owner
            .compare_exchange(thread_pointer(), 0, Ordering::Release, Ordering::Relaxed);
}
