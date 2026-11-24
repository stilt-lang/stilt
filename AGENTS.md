# Stilt

A programming language: its Reference, a reference interpreter and a conformance suite that judge every implementation, and a compiler with a debug back end, a release back end through C, WebAssembly and the rest of its toolchain. [README.md](README.md) gives the folders and their roles, and each folder's README what it holds; [CONTRIBUTING.md](CONTRIBUTING.md) gives the rules in full.

This file is for anyone who works on Stilt with an AI tool. The rules are the same as everyone's: the contributor is responsible for every line, and a large generated change says so in its pull request.

## Commands

- `just ci`: everything CI checks. Run it before calling any change done. It runs the recipes that only pass or fail two at a time from one queue, `fmt-check` and `lint` first, then the longest first, then `latency` and `bench` alone, with each recipe's output in `target/ci/`.
- `just fmt` formats everything, and `just test` runs every unit test.
- **The language.** `just conformance` (the conformance suite against the reference interpreter), `just coverage` (which paragraphs of the Reference the suite cites, and which codes of the registry it expects), `just guide` (the examples of the guide and of the error index), `just examples` (the programs of `examples/` and the compile-time benchmark, under both implementations), `just formal` (the Lean model, then `just proof-map`: the model mapped against the Reference for the site's proof map, failing on a citation of no paragraph or on `sorry` or an axiom of its own).
- **The compiler against the interpreter.** `just parse` (syntax trees), `just check` (diagnostics), `just run` (runs and tests of the suite and the guide's examples, in memory and as built executables, and of programs with errors), `just differential` (generated programs, run and tested by both), `just generated`, `just mutated` and `just stress` (generated programs, ones with a planted mistake, and bodies that stress inference), `just scale` (the 50K- and 100K-line generated projects), `just engine` (commands answered by engines).
- **Tools.** `just formatter` (`stilt fmt` against the pairs of `tests/format/`), `just grammar` (the published GBNF and Lark grammars, regenerated from `reference/03-syntax.md` with no change and keeping every prefix of valid programs viable; `just grammar-generate` writes them), `just ports` (the programs ported to Stilt against what their Rust originals write), `just diagnostics` (the compiler's messages against their snapshots), `just diagnostics-tokens` (each message under 40 tokens), `just site` (the website, built into `target/site` with every internal link checked), `just facts`, `just holes` and `just alternatives` (what `stilt show` and `stilt check --json` report for the suites of `tests/`).
- **Builds and targets.** `just cross` (the suite built by each host for each target; CI runs `just cross-sample`), `just toolchain` (the linker and runtime libraries of `stilt build`), `just dist` (this host's toolchain packed and installed into an empty home), `just sanitizers` and `just debuggers` (on Linux in Docker).
- **Measurements.** `just bench` (the benchmark suite against its Rust baselines, with the budgets of `bench/budgets.toml`), `just latency` (edit-to-diagnostics and the other interactive times, in a release build), `just memory` (an engine's cache across replays of the edit script), `just compare` (the Perceus paper's programs and the suite's against their versions in other languages, against no budget).
- `just nightly` runs a million generated programs, the whole cross matrix, the sanitizers and the debuggers.
- OCaml tools run in the local switch: `opam exec --switch=. -- dune build`. A git worktree has no switch of its own: set `STILT_SWITCH` to the main checkout's path, and every recipe uses that one.

## Rules

- [`reference/`](reference/) is normative. A change to the language changes its paragraphs first, and cites the paragraph it implements.
- The documents in `docs/` describe the language exactly as the Reference states it. When a paragraph changes, update the documents in the same change.
- Expected test output comes from the Reference, never from running an implementation. A diagnostics snapshot is the one exception: it is the compiler's rendering, drafted by `just snapshots-draft` and reviewed before `just snapshots-accept` accepts it.
- Register every new diagnostic code in `reference/errors.toml`, with the paragraph that defines it, and run `cargo run -p stilt-registry`, which generates the code that follows from the registry.
- No stubs, and no edits to a test's expectations without citing the paragraph that justifies them.
- Files stay under 500 lines and functions within 60, split by concern ([CONTRIBUTING.md](CONTRIBUTING.md), Code). `just lint` checks both.
