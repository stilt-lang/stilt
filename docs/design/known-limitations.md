# Known limitations

This page lists what this release of Stilt doesn't do yet, or does only within a limit, and what to do instead. None of these is a bug. A bug is something the [Reference](../../reference/) promises and an implementation doesn't do: report it on the [issue tracker](https://github.com/stilt-lang/stilt/issues).

## Platforms

- **Hosts.** The toolchain runs on macOS on ARM, and on Linux on ARM and x86-64 with glibc 2.31 or later, as on Ubuntu 20.04 and Debian 11 and later. It doesn't run on Alpine, whose C library is musl. There is no Windows toolchain yet: on Windows, use WSL or a Linux container.
- **Targets.** From any host, `stilt build --target` builds for macOS on ARM, Linux on ARM and x86-64, and WebAssembly (`wasm32-wasip1`). See [Builds](../../reference/20-builds.md).
- **Release builds** download clang the first time they run, so the first one needs the network.
- **Release builds on older Linux.** The clang they download needs glibc 2.34 or later, and the libstdc++ of GCC 12 or later (`GLIBCXX_3.4.30`), so it doesn't run on Ubuntu 20.04, on Debian 11 or on Alpine. There, set `STILT_CC` to a clang that runs on the machine ([builds.another-compiler](../../reference/20-builds.md#builds.another-compiler)), or build on a newer system.

## Memory and stacks

- **The reference interpreter** has 512 MiB of heap ([program.exit-statuses](../../reference/04-programs.md#program.exit-statuses)). A compiled program can use all the memory of the machine, or the amount `STILT_HEAP` sets, as in `STILT_HEAP=2G`.
- **Each thread of a compiled program** reserves a 1 GiB stack, and uses only what its calls reach. Some systems refuse that much, such as Linux with strict overcommit (`vm.overcommit_memory=2`). There a thread takes 256 MiB or 16 MiB, so deep recursion overflows the stack sooner. It still goes deeper than [program.recursion-depth](../../reference/04-programs.md#program.recursion-depth) requires.
- **WebAssembly.** A module has at most 4 GiB of memory, and its lengths are 32-bit, so one value holds at most 512 MiB. Each waiting task keeps a stack of about 1.2 MiB, so about 3,400 tasks can wait at once ([wasm.limits](../../reference/20-builds.md#wasm.limits)). Starting a process or opening a socket raises `PermissionDenied`.

## The standard library

- **`std.http`** speaks HTTP/1.1 over plain `http://`, with one request per connection. `serve` answers one connection at a time. To answer several at once, accept each connection yourself and answer it in a task, as [`examples/kv`](../../examples/kv/) does. There is no TLS: to fetch an `https://` URL, run `curl` with `std.process`.
- **`std.net`** has TCP and UDP, and no TLS. Its calls block their task, which `task.threads()` runs beside the others; there is no event loop.
- **`std.regex`** has no backreferences, no lookaround and no flags such as case-insensitive matching. Its classes `\d`, `\w` and `\s` match ASCII only. Backreferences and lookaround can't be matched in linear time, which `std.regex` guarantees.
- **Text.** `std.text` maps case and classifies characters by the tables of Unicode 17.0.0, without the mappings that depend on context or language. No module normalizes text or splits it into grapheme clusters.

## Tools

- **Packages** come from git repositories and local paths. There is no package registry, so `stilt diff` compares two versions that you name.
- **Editors.** The VS Code extension runs the language server. Any editor with a language-server client can run `stilt lsp`, and the tree-sitter grammar in [`editors/tree-sitter/`](../../editors/tree-sitter/) highlights Stilt in editors that use tree-sitter.
- **The playground** runs `check`, `show` and the reference interpreter in your browser. A program's files live in memory and disappear when it ends. It can't start a process, open a socket or call C, and it has less stack than a native run.
- **Compile-time code** runs within a budget of steps and 512 MB of values ([Compile-time sandbox](compile-time-sandbox.md)). One native operation on a huge value counts as one step, so the budget alone doesn't bound its time.

## The proofs

The Lean model in [`formal/`](../../formal/) proves sound a core calculus of Stilt: the values, types, functions, traits and generic functions of the `core` tier, with modes, views, effects and handlers, and shared values. It leaves out, among others, generic records and variant types, generic impls and methods, and the meta and systems tiers; its README lists what it covers. A program is linked to the theorem through the model's export, which writes the programs of the conformance suite in the calculus and runs them in each of its models of memory, and isn't itself proved. The rest of the language is held to the Reference by the conformance suite, which both the reference interpreter and the compiler run, and by differential testing.
