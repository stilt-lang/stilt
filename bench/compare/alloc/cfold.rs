//! cfold's Rust version, `../perceus/cfold/main.rs`, linked with mimalloc.

#[global_allocator]
static ALLOCATOR: mimalloc::MiMalloc = mimalloc::MiMalloc;

#[path = "../perceus/cfold/main.rs"]
mod program;

fn main() {
    program::main();
}
