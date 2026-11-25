<h1 align="center">
  <picture>
    <source media="(prefers-color-scheme: dark)" srcset="brand/logo-on-dark.svg">
    <img src="brand/logo.svg" alt="Stilt" width="340">
  </picture>
</h1>

<p align="center">
  <b>A compiled language whose compiler shows you what your code costs.</b>
</p>

<p align="center">
  <a href="https://stilt.dev">Website</a> ·
  <a href="https://stilt.dev/learn/tour/">Tour</a> ·
  <a href="https://stilt.dev/playground/">Playground</a> ·
  <a href="https://stilt.dev/learn/">Guide</a> ·
  <a href="https://stilt.dev/reference/">Reference</a> ·
  <a href="https://stilt.dev/library/">Library</a> ·
  <a href="https://github.com/stilt-lang/stilt/discussions">Discussions</a>
</p>

<p align="center">
  <a href="https://github.com/stilt-lang/stilt/actions/workflows/ci.yml?query=branch%3Amain"><img src="https://github.com/stilt-lang/stilt/actions/workflows/ci.yml/badge.svg?branch=main" alt="CI"></a>
  <a href="#license"><img src="https://img.shields.io/badge/license-MIT%20or%20Apache%202.0-0F1114" alt="License: MIT or Apache 2.0"></a>
  <a href="docs/design/known-limitations.md"><img src="https://img.shields.io/badge/edition-2027-FF4A2E" alt="Edition 2027"></a>
</p>

Stilt is a compiled programming language. It aims for Go's compile speed, Rust's safety, C++'s performance, Haskell's types and Elm's error messages, with macros and compile-time code that run in your editor. Each feature has one meaning, and the compiler chooses how to build it: quickly in a debug build, for speed in a release build. What you don't write down, the compiler works out and shows you: where each function allocates or copies, whether it can panic or might not end, and which arguments it uses up.

```stilt
fn count_above(xs: List<i64>, limit: i64) -> i64 without alloc {
  var n = 0
  for x in xs { if x > limit { n += 1 } }
  n
}
```

`without alloc` is a promise that the compiler checks: the function, and every function it names, never allocates. A function value it is given isn't covered, since its facts count where it was written ([facts.calls-through-function-values](reference/15-facts.md#facts.calls-through-function-values)). A call of C counts as allocating unless the C function's declaration says it doesn't, a statement that `stilt show` marks as trusted ([c.effects](reference/20-builds.md#c.effects)). Ask what else the compiler knows, and it shows that `n += 1` can overflow:

```console
$ stilt show main.count_above
module main [core]
fn count_above(xs: List<i64>, limit: i64) -> i64 without alloc [overflow] {
  var n: i64 = 0
  for x in xs { if x > limit { n += 1 } } // a `+=` can overflow
  n
}
```

## What Stilt gives you

Each of these is taught in the guide:

- **Values, with no lifetimes to write.** Every value behaves as an independent copy. The compiler updates it in place when nothing else holds it, and no tracing garbage collector runs ([Values and types](docs/guide/02-values.md)).
- **Facts you can ask for, and limits you can set.** `stilt show` prints what each function does that its types don't say, such as `panic`, `overflow`, `alloc` or `div`. A `without` clause turns a fact into a promise that the checker keeps.
- **Effects in the signature.** A function that prints, raises an error or performs an effect of your own says so after a `/`. Handlers give your effects their meaning ([Errors and effects](docs/guide/05-errors.md), [Effects, tasks and parallelism](docs/guide/17-effects.md)).
- **Changes without references.** An `inout` parameter changes the caller's place, and the compiler refuses two overlapping accesses at once ([Parameter modes](docs/guide/07-modes.md)).
- **Macros and compile-time code that your editor understands.** Compile-time code is Stilt, run in a sandbox with the same result each time ([Pattern macros](docs/guide/16-macros.md), [Compile-time code](docs/guide/18-compile-time.md)).
- **Two builds, one meaning.** A debug build goes through Cranelift, to compile fast. A release build goes through C, to run fast ([Builds](reference/20-builds.md)).

An error says what went wrong, why the rule is there, and what to write instead:

```console
$ stilt check
── EFFECT THAT DOESN'T FIT THE ROW ──────────────────── src/main.lt:5:3  [E0502]

This performs `io`, which the row doesn't declare:

  5 │   print(greeting("arena"))
    │   ^^^^^^^^^^^^^^^^^^^^^^^^

A function's row lists the effects it performs, as `/ io` for printing, so that
its callers see them. Add the effect to the row.

To fix it, declare `io` in the signature:

  4 │ fn main() / io {
    │          +++++
```

## Get started

[The playground](https://stilt.dev/playground/) checks, shows and runs a program in your browser, with nothing to install.

The installer puts `stilt` in `~/.stilt/bin`, on macOS on ARM and on Linux on ARM and x86-64:

```sh
curl -sSf https://raw.githubusercontent.com/stilt-lang/stilt/main/install.sh | sh
```

It installs the latest [release](https://github.com/stilt-lang/stilt/releases). On Linux, the clang that release builds download needs glibc 2.34 and GCC 12's libstdc++ or later; [known limitations](docs/design/known-limitations.md#platforms) says what to do on older systems. Until the first one, 2027.1.0, is published, [build Stilt from this repository](#building).

Then create a program, run it, test it, and ask what the compiler worked out:

```sh
stilt new hello && cd hello
stilt run
stilt test
stilt show main
```

Where you go next depends on what you know:

| If you | Read |
| --- | --- |
| Want to build something | [A tour](docs/guide/01-tour.md), thirty minutes |
| Know [Rust](docs/guide/for-rust-programmers.md), [Go](docs/guide/for-go-programmers.md), [Python](docs/guide/for-python-programmers.md), [TypeScript](docs/guide/for-typescript-programmers.md) or [Swift](docs/guide/for-swift-programmers.md) | The page that maps it onto Stilt |
| Want to solve one task | [The cookbook](docs/guide/cookbook.md) |
| Want to know why Stilt is this way | [Its design](docs/guide/10-design.md) |

For highlighting, diagnostics and the facts beside your code, see [the editors](editors/): VS Code, Zed, Neovim, Helix and Emacs.

## What is in this repository

This repository holds all of Stilt:

- [the Reference](reference/), which defines the language paragraph by paragraph;
- `stilt-ref`, a reference interpreter, and a conformance suite, which judge every implementation against the Reference on what programs print, how they end and which errors they report; the facts that `stilt show` reports, which 31 paragraphs define, are checked against the compiler alone;
- `stilt`, the compiler, which checks programs, runs them while you edit them, and builds executables for macOS on ARM, Linux on ARM and x86-64, and WebAssembly, with debug builds through Cranelift and release builds through C;
- `stilt test`, packages, a formatter, a REPL, a language server, and a standard library written in Stilt.

The language has four tiers. `core`, `advanced` and `meta` are complete. Of `systems`, calls into C and functions exported to C are built. The first edition of the language is 2027.

[Known limitations](docs/design/known-limitations.md) lists what this release doesn't do yet, and [Versions and compatibility](reference/21-versions.md) says what each release keeps from the last.

### Folders

Each top-level folder has one role, and a README that says what it holds.

| Folder | Role |
| --- | --- |
| [`reference/`](reference/) | The Reference, which defines the language paragraph by paragraph, with each chapter's rationale, the grammar's published forms and the registry of diagnostic codes |
| [`std/`](std/) | The standard library's sources, which every implementation reads |
| [`interpreter/`](interpreter/) | `stilt-ref`, the reference interpreter, in OCaml 5, which every other implementation is checked against |
| [`compiler/`](compiler/) | `stilt`, the compiler, in Rust, one crate per phase |
| [`brand/`](brand/) | The logo, the mark and its cuts for small sizes, and the images made from them |
| [`editors/`](editors/) | The editor extensions, VS Code's and Zed's, which highlight Stilt and run `stilt lsp`, and the tree-sitter grammar that Zed, Neovim and Helix read |
| [`playground/`](playground/) | The playground, the site's page that checks, shows and runs a program in the browser: the compiler's `check` and `show` built for WebAssembly, the reference interpreter built for JavaScript, and the page's scripts |
| [`site/`](site/) | The website, built with Astro from the repository's documents and what the compiler prints: the guide, the Reference, the library, the error index and the playground |
| [`examples/`](examples/) | Programs written in Stilt, with their tests and samples: a CSV query tool, an interpreter of a small language, a Markdown converter, a JSON query tool, the Game of Life, a ray tracer, a bytecode interpreter, a key-value store served over HTTP and a library that reads command-line options from a record's type |
| [`conformance/`](conformance/) | The conformance suite, the Reference's executable form, whose tests judge every implementation |
| [`tools/`](tools/) | The programs that test and measure an implementation: the conformance runner, the program generator, the grammar generator, the latency harness, fuzz targets and studies |
| [`tests/`](tests/) | The toolchain's test suites: diagnostics snapshots, the formatter's pairs, and the programs whose facts, holes, alternatives and costs `stilt show` must report |
| [`bench/`](bench/) | The benchmark suite and its Rust baselines, and the compile-time benchmark |
| [`formal/`](formal/) | A Lean 4 model of the `core` calculus, with its typing and mode rules |
| [`docs/`](docs/) | The guide to the language, the error index and the design documents |

[`AGENTS.md`](AGENTS.md) gives the commands and rules that people and agents follow. The project's rules and process are in [`CONTRIBUTING.md`](CONTRIBUTING.md), [`GOVERNANCE.md`](GOVERNANCE.md) and [`SECURITY.md`](SECURITY.md); a change to the language starts as an [RFC](https://github.com/stilt-lang/stilt-rfcs); [`RELEASING.md`](RELEASING.md) and [`changes/`](changes/) describe releases.

## Building

You need:

- Rust, through [rustup](https://rustup.rs), at the version and with the targets that [`rust-toolchain.toml`](rust-toolchain.toml) pins;
- a C compiler, such as Xcode's command-line tools on macOS or `gcc` on Linux, which builds ring, the cryptography of `stilt`'s HTTPS. An installed `stilt` needs nothing else to check and run programs, and fetches its C compiler for the first release build;
- libffi, through which the reference interpreter calls C, which macOS's SDK holds and Linux's `libffi-dev` gives, and zlib, which the conformance tests of calling C link, which macOS holds and Linux's `zlib1g-dev` gives;
- [opam](https://opam.ocaml.org) 2.2 or later;
- Lean, at the version that [`formal/lean-toolchain`](formal/lean-toolchain) pins, which [elan](https://github.com/leanprover/elan) installs;
- [just](https://github.com/casey/just);
- [Docker](https://www.docker.com) running, for `just sanitizers` and `just debuggers`, which run Linux, and on an aarch64 Mac for `just cross`, which emulates the x86-64 Linux host and target;
- on macOS, lldb, and Developer Mode on (`sudo DevToolsSecurity -enable`), so that the debugger tests can run programs under it.

Create the repository's local opam switch once, build, then run everything CI runs:

```sh
just setup
just ci
```

`just setup` creates the switch with `opam switch create . 5.5.2 --deps-only --with-test --with-dev-setup`, fetches the pinned toolchains and builds.

`just` lists the other commands. `just dist` packs this host's toolchain into an archive, and [`install.sh`](install.sh) installs one: `STILT_DIST=target/dist sh install.sh` puts `stilt` in `~/.stilt/bin`.

## Contributing

Read [CONTRIBUTING.md](CONTRIBUTING.md) first. Language changes start as an [RFC](https://github.com/stilt-lang/stilt-rfcs), then in the Reference, and every paragraph needs tests. Ask questions in [Discussions](https://github.com/stilt-lang/stilt/discussions), and report a vulnerability as [SECURITY.md](SECURITY.md) says. Everyone follows the [code of conduct](CODE_OF_CONDUCT.md).

## License

Code is distributed under the terms of both the [MIT license](LICENSE-MIT) and the [Apache License, Version 2.0](LICENSE-APACHE), at your option. That covers the compiler, the reference interpreter, the tools, the standard library, the editors' extensions, the Lean model, the examples, the benchmarks and the **conformance suite** in [`conformance/`](conformance/), which is licensed so that other implementations of Stilt can use it, and the published grammars in [`reference/grammar/`](reference/grammar/). The tests of `conformance/ported/` translated from the test suites of Koka, Effekt, Swift and Hylo are under those projects' licenses, which [NOTICE](NOTICE) gives.

A program that `stilt build` writes holds Stilt's runtime library, under the licenses of the code, with Rust's standard library and the crates the runtime uses, under the MIT license or the Apache License 2.0. One built for Linux also holds musl, under the MIT license, and LLVM's libunwind, and one built for WebAssembly wasi-libc and LLVM's builtins, which the Apache License 2.0 with LLVM's exception covers and which ask for no notice in a built program. The MIT license asks that its notice go with copies, so a program you give out in binary form carries the notices of Rust's standard library, of the runtime's crates and, built for Linux, of musl. Each release's archive holds them: `THIRD-PARTY-LICENSES` lists every part and crate, with their notices, and `rust/` holds Rust's.

The prose is distributed under the [Creative Commons Attribution 4.0 International license](LICENSE-CC-BY-4.0): the chapters of the Reference in [`reference/`](reference/), the guide in [`docs/guide/`](docs/guide/), the error index in [`docs/errors/`](docs/errors/), the design documents in [`docs/design/`](docs/design/), and [`docs/commands.md`](docs/commands.md) and [`docs/writing.md`](docs/writing.md). The Stilt programs in those documents are also available under the licenses of the code.

The logo and the other drawings of [`brand/`](brand/), and the copies of them that the site and the editors' extensions hold, are under the same Creative Commons license.

Unless you explicitly state otherwise, any contribution you intentionally submit for inclusion in this project is licensed as the files it changes are, without any additional terms or conditions: inbound equals outbound, and there is no contributor license agreement.
