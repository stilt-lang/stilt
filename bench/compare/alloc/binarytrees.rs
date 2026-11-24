//! binarytrees's Rust version, `../perceus/binarytrees/main.rs`, linked with mimalloc.

#[global_allocator]
static ALLOCATOR: mimalloc::MiMalloc = mimalloc::MiMalloc;

#[path = "../perceus/binarytrees/main.rs"]
mod program;

fn main() {
    program::main();
}
