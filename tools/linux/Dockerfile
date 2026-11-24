# The Linux machine of `just sanitizers` and `just debuggers`, which Docker runs for the host's
# architecture: Rust at the version, with the components and targets, that rust-toolchain.toml
# pins, which builds the conformance runner and a build of the compiler for this machine; a
# pinned nightly, whose rustc builds the compiler and its runtime with AddressSanitizer, which
# brings LeakSanitizer with it, or with ThreadSanitizer, with the standard library's source,
# which it builds instrumented too (goal no-memory-errors); LLVM's symbolizer, which names the
# functions in a sanitizer's report; gdb, with QEMU's user-mode emulation of x86-64 for the
# executables `stilt build` writes for that target (debuggable-builds); and zlib's shared library, which
# the conformance tests of c.linking and c.both-implementations link.
FROM rust:1.99-slim
RUN apt-get update \
    && apt-get install -y --no-install-recommends llvm gdb gdb-multiarch qemu-user zlib1g-dev \
    && rm -rf /var/lib/apt/lists/*
RUN rustup toolchain install 1.99 --profile minimal --component clippy,rustfmt \
        --target aarch64-apple-darwin,x86_64-unknown-linux-musl \
    && rustup toolchain install nightly-2026-10-29 --profile minimal --component rust-src
