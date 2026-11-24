#!/usr/bin/env bash
# `musl.sh TRIPLE CARGO-ARGS...` runs cargo for TRIPLE, a Linux target of musl, on this machine:
# `just cross` builds the compiler for x86-64 Linux with it, and `just debuggers` the compiler
# and its debugger tests for the Linux machine of the host's architecture, which then only runs
# them. musl's C library and start files come with Rust's target, so the executables are static
# and run on any Linux, and Rust's own lld links them. ring, the cryptography of `stilt`'s
# HTTPS, has C and assembly of its own: clang compiles them without a Linux sysroot, as ring's
# build does for musl's other architectures, and LLVM's archiver, from rustup's llvm-tools,
# bundles them.
set -euo pipefail
triple=$1
shift
rustc=$(rustup which rustc)
sysroot=$("$rustc" --print sysroot)
host=$("$rustc" -vV | sed -n 's/^host: //p')
tools=$sysroot/lib/rustlib/$host/bin
rustup target add "$triple" > /dev/null 2>&1
rustup component add llvm-tools > /dev/null 2>&1
upper=$(echo "$triple" | tr 'a-z-' 'A-Z_')
lower=$(echo "$triple" | tr '-' '_')
export "CARGO_TARGET_${upper}_LINKER=$tools/rust-lld"
export "CARGO_TARGET_${upper}_RUSTFLAGS=-C linker-flavor=ld.lld -C link-self-contained=yes"
export "CC_$lower=$(command -v clang)"
export "AR_$lower=$tools/llvm-ar"
export "CFLAGS_$lower=-nostdlibinc -DRING_CORE_NOSTDLIBINC=1 -U__musl__ -D__MM_MALLOC_H"
RUSTC=$rustc exec cargo "$@" --target "$triple"
