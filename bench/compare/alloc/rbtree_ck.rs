//! rbtree_ck's Rust version, `../perceus/rbtree_ck/main.rs`, linked with mimalloc.

#[global_allocator]
static ALLOCATOR: mimalloc::MiMalloc = mimalloc::MiMalloc;

#[path = "../perceus/rbtree_ck/main.rs"]
mod program;

fn main() {
    program::main();
}
