//! Gives each binary's main thread the stack that the comparisons give every Rust program on
//! macOS, 512 MiB, which cfold's recursion a million calls deep needs (../../src/compare/toolchains.rs).

fn main() {
    if std::env::var("CARGO_CFG_TARGET_OS").as_deref() == Ok("macos") {
        println!("cargo:rustc-link-arg-bins=-Wl,-stack_size,0x20000000");
    }
}
