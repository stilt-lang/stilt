//! Links the playground's compiler for WebAssembly. Its main thread's stack is as large as a main
//! thread's on the hosts Stilt supports, since checking recurses as deep as an expression is
//! nested (`stilt_db::parallel`), and procedural macros run on it. And the runtime it links,
//! for the formatting of values that `std.meta` and the facts share, holds the functions that
//! switch a compiled program's stacks, which take the stack pointer from functions that a
//! compiled program's C defines (`stilt-codegen-c`'s `assemble`): the module imports those,
//! which `undefined.txt` lists, and the checker never calls them.

use std::env;
use std::path::Path;

/// The size of the main thread's stack, as `stilt_db::parallel` gives each thread.
const STACK: usize = 16 * 1024 * 1024;

fn main() {
    let manifest = env::var_os("CARGO_MANIFEST_DIR").expect("cargo sets it");
    let undefined = Path::new(&manifest).join("undefined.txt");
    println!("cargo::rerun-if-changed={}", undefined.display());
    if env::var("CARGO_CFG_TARGET_ARCH").is_ok_and(|arch| arch == "wasm32") {
        println!("cargo::rustc-link-arg-bins=-zstack-size={STACK}");
        println!(
            "cargo::rustc-link-arg-bins=--allow-undefined-file={}",
            undefined.display()
        );
    }
}
