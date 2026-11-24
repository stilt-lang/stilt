//! nqueens's Rust version, `../perceus/nqueens/main.rs`, linked with mimalloc.

#[global_allocator]
static ALLOCATOR: mimalloc::MiMalloc = mimalloc::MiMalloc;

#[path = "../perceus/nqueens/main.rs"]
mod program;

fn main() {
    program::main();
}
