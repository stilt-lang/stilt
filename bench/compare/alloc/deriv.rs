//! deriv's Rust version, `../perceus/deriv/main.rs`, linked with mimalloc.

#[global_allocator]
static ALLOCATOR: mimalloc::MiMalloc = mimalloc::MiMalloc;

#[path = "../perceus/deriv/main.rs"]
mod program;

fn main() {
    program::main();
}
