//! Stacks of their own, which the bodies of handlers that take control and resume run on
//!: the runtime switches from one stack to another and back, and since a
//! body resumes at most once, no stack is ever copied.
//!
//! A [`Context`] is a stack that code runs on: the thread's own, or one made for a body. A new
//! context starts at an entry function when it is first switched to, and its entry's last act
//! is a switch back to the context that ran it, marked as the last. The native targets switch
//! registers between stacks the runtime maps (`native`); WebAssembly, which can't reach its
//! own stack, unwinds and rewinds the frames of a body with binaryen's Asyncify (`wasm`;
//! wasm.handlers-that-resume).

#[cfg(not(target_family = "wasm"))]
mod native;
#[cfg(stilt_tsan)]
mod tsan;
#[cfg(target_family = "wasm")]
mod wasm;

#[cfg(not(target_family = "wasm"))]
pub(crate) use native::{Context, started, switch};
#[cfg(target_family = "wasm")]
pub(crate) use wasm::{Context, started, switch};

/// The entry of a new context, given the argument it was made with. On the native targets it
/// never returns, since its last switch leaves its stack for good; on WebAssembly its last
/// switch returns, and the entry then returns to the context that ran it.
pub(crate) type Entry = unsafe extern "C" fn(usize);
