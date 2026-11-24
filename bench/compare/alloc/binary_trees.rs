//! binary_trees's Rust version, `../../programs/binary_trees/baseline.rs`, linked with mimalloc.

#[global_allocator]
static ALLOCATOR: mimalloc::MiMalloc = mimalloc::MiMalloc;

#[path = "../../programs/binary_trees/baseline.rs"]
mod program;

fn main() {
    program::main();
}
