//! rbtree's Rust version, `../perceus/rbtree/main.rs`, linked with mimalloc.

#[global_allocator]
static ALLOCATOR: mimalloc::MiMalloc = mimalloc::MiMalloc;

#[path = "../perceus/rbtree/main.rs"]
mod program;

fn main() {
    program::main();
}
