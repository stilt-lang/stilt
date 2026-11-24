# The comparisons with other languages

Stilt's release builds against other languages on three sets of programs, and a tool written in Stilt against the tools it imitates, which `stilt-bench compare` ([`../src/compare.rs`](../src/compare.rs)) builds, checks and times against no budget. `just compare` runs it, and writes `target/compare/results.md` and `results.json`: each program's time in each language with the spread of its runs, its instructions and its peak memory, the machine and how busy it was, and each toolchain's version and flags.

The last full run, at commit 1e132078 on 2026-11-24 on an Apple M4, is kept in [`results.md`](results.md), and that of `stilt-bench shootout` beside it in [`edit-loop.md`](edit-loop.md); each says the machine, how busy it was and each toolchain's version. Stilt's release builds are 0.86 of Rust's time over the suite as a geometric mean, 0.50 over the Perceus paper's programs, 0.73 over the programs that allocate most against Rust linked with mimalloc, and 1.04 over `std.par` against Rayon.

| Path | Contents |
| --- | --- |
| [`results.md`](results.md) | The last run of `just compare`, with its date, machine and toolchains |
| [`edit-loop.md`](edit-loop.md) | The last run of `stilt-bench shootout`: the edit loop of a 50,000-line project in each language |
| [`perceus/`](perceus/) | The six programs of the Perceus paper, each in Stilt (`main.lt`), Rust (`main.rs`), Koka (`main.kk`), OCaml (`main.ml`), Haskell (`Main.hs`), Swift (`main.swift`) and Java (`Main.java`) |
| [`programs/`](programs/) | The benchmark suite's programs in Go (`main.go`), Swift (`main.swift`) and OCaml (`main.ml`), beside the Stilt programs and Rust baselines of [`../programs/`](../programs/) |
| [`par/`](par/) | Three programs of `std.par`, each in Stilt (`main.lt`) and in Rust with Rayon (`main.rs`), the Rust versions the binaries of the Cargo package `par/Cargo.toml`, which `--cargo` builds with `--rustc` |
| [`tools/`](tools/) | `pick.queries`, the queries that [`examples/pick`](../../examples/pick/), jq and jaq each run |
| [`toolchains.sh`](toolchains.sh) | Downloads Go's and Koka's official release archives into `target/toolchains/`, checked against their SHA-256, and installs nothing elsewhere |

## The Perceus paper's programs

Reinking, Xie, de Moura and Leijen's *Perceus: Garbage Free Reference Counting with Reuse* (PLDI 2021) compares Koka with OCaml, Haskell, Swift, Java and C++ on programs that allocate much and compute little; its versions are in the Koka repository's `test/bench/`. These are written afresh from the same algorithms, at the same sizes:

- **rbtree** inserts 4,200,000 keys into a red-black tree, every tenth with the value true, and folds over the tree to count them.
- **rbtree_ck** does the same, keeping every fifth tree it makes, so the trees share most of their nodes.
- **deriv** differentiates x^x ten times, simplifying each derivative as it is built; the last counts 40 million nodes, many of them shared.
- **nqueens** finds the 73,712 placements of 13 queens, row by row, each partial placement a list that shares its tail with the others that extend it.
- **cfold** builds an expression of 2^20 sums, reassociates it into a chain a million deep, folds its constants, and evaluates it before and after.
- **binarytrees** is the Benchmarks Game's binary-trees at depth 21, on one thread in every language, as the suite's is.

## Rules

- **The same algorithm, written as each language's programmers write it.** Where the algorithm shares structure, the Rust versions share it through `Rc` (rbtree_ck, deriv and nqueens), and where nothing is shared they own their trees and rebuild them in the nodes they take apart (rbtree, cfold, binarytrees). The Haskell versions give their data strict fields, as the paper's do, so that they do the same work, and binarytrees turns off common-subexpression elimination, which would make one tree of the two equal subtrees of each node. The Koka versions of rbtree and nqueens use 32-bit integers, as the paper's do. The Java versions are records, sealed interfaces and pattern matching. The suite's programs follow its rules ([`../README.md`](../README.md#rules)), with each language's standard library; the OCaml version of string-heavy writes the search and replacement of substrings that OCaml's standard library lacks.
- **The same output.** Every version prints what the Rust version prints, which the runner checks on each run.
- **Deep stacks.** cfold recurses a million calls deep, so every language whose build chooses the size of the main thread's stack gets 512 MiB, the most that the arm64 linker gives a macOS executable: Rust and Swift by the linker on macOS, and on Linux by the stack's limit, which the runner raises; Koka by `--stack=512M`; Java by `-Xss512m`. OCaml 5, GHC and Go grow their stacks themselves. A version that ends with an error, as a Stilt program does when it outgrows the heap or the stack its runtime gives it ([program.exit-statuses](../../reference/04-programs.md#program.exit-statuses)), is reported with the error.

## Measurement

Each version is built with its language's release flags: `stilt build --release`, `rustc -C opt-level=3` as in [`../README.md`](../README.md#measurement), `koka -O2`, `ocamlopt` (with `-O3` where the compiler has flambda), `ghc -O2`, `swiftc -O -wmo`, `javac` and `java`, and `go build`. Each runs once untimed, since a system may check a new executable on its first run, and then the versions of a program take turns, each at least 5 times and as many more as its runs take to add up to a second. A version's time is that of its runs' counts added together, divided by their number: its cycles on the performance cores at the reference machine's clock, or its wall time where that is less, as for Java's threads, by the Timing rule of the [goals](../../docs/design/goals.md#how-to-read-the-goals), which the [meter](../../tools/meter/) reads. Its spread is the standard deviation of its runs' times over their mean. Instructions are the mean of its runs', and change least when other programs share the machine; peak memory is the least of its runs' peak resident memory. `--filter`, `--languages`, `--runs` and `--seconds` narrow or lengthen a run.
## `std.par` against Rayon

Three programs that `std.par` runs in parallel ([par.std-par](../../reference/14-tasks.md#par.std-par)), each in Stilt and in Rust with [Rayon](https://github.com/rayon-rs/rayon), the Rust versions binaries of the Cargo package in `par/`, a workspace of its own whose `Cargo.lock` fixes Rayon's version:

- **mandelbrot** counts the suite's mandelbrot grid at 4,000 × 4,000, a row to each call of `par.map`'s closure and of Rayon's `map`.
- **primes** counts the primes below 8,000,000 by trial division, in chunks of 10,000 that `par.map` counts and `par.fold` adds up, and that Rayon's `map` counts and `sum` adds up. The chunks near the bound take longest, so the work is uneven.
- **states** advances 2,000,000 generators 400 steps each in place, with `par.each` and Rayon's `par_iter_mut`, then folds their states into one checksum.

Each program runs on 1 thread and on every number up to one per core, which `STILT_THREADS` and `RAYON_NUM_THREADS` set, each a row of the report, and every run is checked against what the Rust version prints. A Stilt program prints the same on every number of threads, as [par.sequential-meaning](../../reference/14-tasks.md#par.sequential-meaning) says it must, and the check holds it to it in the same run. On a machine whose cores aren't all alike, as Apple's performance and efficiency cores aren't, a thread beyond the fast cores adds less than the ones before it.

## Against Rust with mimalloc

A Stilt program allocates through its runtime's cache of freed small blocks, one list for each size, and a Rust program through the system's allocator unless it links another ([`../README.md`](../README.md), Allocators), so on the programs that allocate most the suites above measure the allocators as much as the code. [`alloc/`](alloc/) is a Cargo package whose binaries are the Rust versions of those programs as they are, the Perceus paper's six and the suite's binary-trees, each compiled as a module of a binary that sets mimalloc as the global allocator, the choice of a Rust program built to allocate many small objects. Each runs against its Stilt program, and must print what the Rust version prints.

## `examples/pick` against jq and jaq

[`examples/pick`](../../examples/pick/) runs a query written in a part of jq's language, as [jq](https://jqlang.org) and [jaq](https://github.com/01mf02/jaq) do. Each query of `tools/pick.queries` is a row, run by the three on a document of 300,000 books, about 80 MB, which `stilt-bench compare` writes from a fixed sequence of pseudo-random numbers ([`../src/compare/input.rs`](../src/compare/input.rs)), each printing its results on one line with `-c`. jq is the reference here: the others must print what it prints, and their times are measured against its. `--jq` and `--jaq` name the tools, which are run as they are installed, and one that isn't found is left out.

## The edit loop

`stilt-bench shootout` ([`../src/shootout.rs`](../src/shootout.rs)) writes the same project in Stilt, Rust, Go, OCaml and Swift, about 50,000 lines in each (`--lines`): modules of a record type and 20 functions, each function calling its namesake in the module before it, so that each module depends on the one before it, as a layered program's do. Each version is written as its language's programmers write it, Go's with a package for each module, and every built version must print what the Stilt version prints. It then times, by the wall clock, as a programmer waits:

- **a clean check and a clean debug build**, each from no cache, `--runs` times: `stilt check` and `stilt build`, which start the program's engine; `cargo check` and `cargo build`; `go build`, also Go's check, since Go has no command that only checks, from a cache that holds only Go's own library, which every other language ships compiled; `dune build @check` and `dune build`; and `swift build`, also Swift's check;
- **an edit to diagnostics**, warm, `--edits` times: from an edit that gives the middle module a type error to the check that reports it, and from the edit that fixes it again to a clean check;
- **an edit to the running program**: from an edit that changes what the middle module computes to the running program printing the new value. For Stilt that is `stilt run`, which patches each edit into the program as it runs; for the others, an incremental debug build and a start of the program.

It writes `results.md` in its output directory, `target/shootout`, with the machine and each tool's version. `--languages` narrows a run, and a language whose tool isn't found is left out. Zig isn't among the languages, its incremental compilation being experimental.
