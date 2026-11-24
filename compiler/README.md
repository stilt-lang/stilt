# Compiler

`stilt`, the compiler, is a Rust workspace built around one query database: every phase is a cached function of its inputs, so an edit redoes only the work it affects. Its front end and both back ends are checked against the [reference interpreter](../interpreter/), which shares no code with it.

This page is a guide for changing it: the crates, the way from text to machine code, the database and what an edit invalidates, where each fact is inferred, how hot patching and the C back end work, and where to start. [Compiler architecture](../docs/design/compiler-architecture.md) gives the design and its choices, and [Compiler internals](../docs/design/compiler-internals.md) how each command and feature is implemented, in detail.

## The crates

Each crate's `//!` header says what it owns and what it depends on. A crate depends only on the crates its row lists: a phase never depends on a later one, and a call that would go backwards goes through a hook that the later crate installs, as name resolution runs procedural macros through the host that `stilt-meta` installs (`stilt_hir::procs::install`).

| Crate | Owns | Depends on |
| --- | --- | --- |
| [`stilt-diag`](stilt-diag/) | The diagnostic record, the registry's codes, generated from `reference/errors.toml` into `src/codes.rs`, and the renderings for people and as JSON | nothing |
| [`stilt-syntax`](stilt-syntax/) | The lexer, the parser and the lossless syntax tree; the parse of a macro's tokens as one form | diag |
| [`stilt-fmt`](stilt-fmt/) | The formatter, from the lossless tree | syntax |
| [`stilt-edit`](stilt-edit/) | A module's parts, their paths and hashes, edits and fixes as edits | syntax, fmt |
| [`stilt-pkg`](stilt-pkg/) | Manifests, dependencies, fetching, versions and the release toolchain's archive | diag, syntax |
| [`stilt-runtime`](stilt-runtime/) | The runtime of compiled programs: objects and their counts, the natives of the standard library, the entry | nothing |
| [`stilt-db`](stilt-db/) | The query database, its inputs and their durability, and the running of queries across cores | diag, syntax, pkg |
| [`stilt-hir`](stilt-hir/) | Module scopes, declarations, name resolution and the expansion of macros | diag, syntax, db |
| [`stilt-types`](stilt-types/) | Type checking into typed bodies, the checks that read them, the inferred facts and verification | diag, syntax, pkg, db, hir |
| [`stilt-mir`](stilt-mir/) | Lowering to the MIR, the layout of values, the per-function optimizer and specialization | diag, syntax, db, hir, types |
| [`stilt-rc`](stilt-rc/) | Consumption, inferred modes, `copy`, and the reference counting of the MIR, with reuse in place | diag, syntax, db, hir, types, mir |
| [`stilt-meta`](stilt-meta/) | The compile-time interpreter, which runs procedural macros | syntax, db, hir, types, mir, runtime |
| [`stilt-codegen-clif`](stilt-codegen-clif/) | The debug back end: Cranelift, the JIT, objects and hot patching | db, mir, runtime |
| [`stilt-codegen-c`](stilt-codegen-c/) | The release back end: the counted MIR as C11 | mir, runtime |
| [`stilt-lsp`](stilt-lsp/) | The Language Server Protocol, the editor's buffers, and a backend that answers | nothing |
| [`stilt-ide`](stilt-ide/) | What `stilt show` and the editor show: code with its inferred facts, the editor's answers, and a diagnostic's place and fixes as edits of parts | diag, syntax, fmt, edit, runtime, db, hir, types, mir, rc, lsp |
| [`stilt-cli`](stilt-cli/) | The `stilt` command: every command, the engine, the REPL, linking and libraries | every crate above |

Only `stilt-runtime` and `stilt-codegen-clif` use `unsafe`, each block with a `SAFETY:` comment; every other crate forbids it, which `just lint` checks.

## From text to machine code

```text
text ─ stilt-syntax ─▶ lossless tree (one per file)
     ─ stilt-hir ────▶ scopes, declarations, resolved bodies, with every macro use expanded
     ─ stilt-types ──▶ typed bodies, diagnostics, inferred facts, proved checks
     ─ stilt-mir ────▶ the MIR of each function the entry reaches, optimized one function at a time
     ─ stilt-rc ─────▶ the same MIR with its reference counting
     ─┬ stilt-codegen-clif ─▶ machine code in memory (run, repl, test) or an object (build)
      └ stilt-codegen-c ────▶ C11 for clang (build --release)
       + stilt-runtime, called in process or linked with rust-lld
```

1. **Parsing.** `stilt_db::parse` turns a file into a lossless tree. A file with a syntax error is read a part at a time, and each part keeps its first error (errors.parts).
2. **Names.** `stilt_hir::def_map` lists the modules, `module_scope` gives each module's names, `declarations` every signature without positions, and `resolve_module` resolves a module's bodies. Uses of pattern macros expand where they are written (`stilt-hir/src/lower/expand.rs`); a procedural macro's use asks the host, `stilt-meta`, which runs the macro's typed body in its own interpreter and gives back tokens.
3. **Types.** `stilt_types::infer_body` checks one body against the signatures it names and elaborates it into a `tast::TypedBody`. The analyses that read typed bodies follow it, and `check_in_parallel` gives a program's diagnostics, in the same order on any number of threads.
4. **MIR.** `stilt_mir::functions` lowers one function, and its closures, to a control-flow graph over word-sized locals; a value is the words of its type's layout. `stilt_mir::Walk` finds what the entry reaches.
5. **Counting.** `stilt-rc` infers which parameters each function consumes (`stilt_rc::consumed`), inserts the `Dup` and `Drop` statements, and builds a new value in the memory of one released on the same path, handing over its fields' counts (`stilt-rc/src/reuse.rs`).
6. **Code.** A debug build compiles the counted MIR with Cranelift (`stilt_codegen_clif::jit` and `object`); a release build specializes it and writes it as C (below).

## The query database

The steps up to the MIR, and what a function consumes, are salsa queries of `stilt-db`'s database, which the command line, the language server, agents and running programs share in the program's engine. The engine keeps each function's counting and machine code from one build to the next, so a build counts and compiles only the functions whose MIR an edit changed.

- **Inputs.** A program file's contents change with each edit, the list of its files when one is added or removed, and the standard library and the files' places never. Each input carries that durability, so an edit never checks again what read only more durable inputs.
- **No positions.** The results that later phases read hold no positions: declarations are separate from bodies, and a body's positions are relative to its start. An edit inside one body leaves every signature, and so every other body's type checking, unchanged, and code that only moves keeps its body's results.
- **What an edit runs again.** Editing a body checks that body again, and lowers again the functions whose MIR it changes; adding an item resolves again only the modules that look that name up in its module. A change to what a function consumes changes its callers' MIR, so they are counted and compiled again too.
- **Parallel work.** Bodies are checked, functions lowered, counted and compiled across the machine's cores, each thread with its own handle, and the results gathered in a fixed order, so the output is the same byte for byte on any number of threads.

The incremental tests are in `stilt-db/src/tests.rs`, `stilt-hir/src/tests.rs` and `stilt-types/src/tests.rs`; `just latency` and `just memory` measure the engine across an edit script.

## Where each fact is inferred

The facts of [the table of facts](../reference/15-facts.md#facts.inferred-facts) and the others that `stilt show` prints:

| Fact | Inferred in |
| --- | --- |
| `panic`, `overflow`, `alloc`, `div` and the capabilities | `stilt-types/src/analyses/implicit/`: `sites.rs` finds each body's operations, `fixed.rs` solves the fixed point over what bodies name, `capabilities.rs` lists the natives that have one, and `limits.rs` checks `without` |
| `locks` | `stilt-types/src/analyses/implicit/locks.rs` |
| `copy` and the copies at calls | `stilt-rc/src/promises.rs` |
| In-place parameters | `stilt-types/src/analyses/implicit/in_place.rs` |
| Consumed parameters | `stilt-rc/src/consume.rs` and `stilt-rc/src/queries.rs` |
| Modes of bindings | `stilt-rc/src/modes.rs` |
| `unsafe` and `foreign` | `stilt-types/src/facts/unsafe_code.rs` |
| Proved checks | the rules of acceptance in `stilt-types/src/accept.rs`, and the analysis that only release builds read in `stilt-types/src/verify.rs` |
| Atomic sites | `stilt-types/src/facts/atomic.rs` |
| A module's tier | `stilt-types/src/facts/views.rs` (`tier`) |
| Types that can form a cycle | `stilt-types/src/cycles.rs` |
| What a dependency needs a grant for | `stilt-types/src/packages.rs` |

`stilt-ide/src/show/facts.rs` gathers them for `stilt show` and the language server.

## Hot patching

`stilt run` compiles the program into its own process and patches each edit into it while it runs (`stilt-cli/src/run.rs`). Its code comes from the engine, or from a database of its own when no engine runs.

- Every function is called through a slot that holds the address of its latest code, in calls, function values and dictionaries alike (`stilt-codegen-clif/src/module.rs`). A patch compiles the functions whose MIR changed and stores their new addresses, so the next call runs the new code and the program keeps its state.
- `run` keeps the last walk of what the entry reaches. After an edit, the queries prove most functions unchanged, and only the functions lowered again, or reached for the first time, are counted and compiled.
- A function whose convention changed keeps a slot for each earlier one, holding a bridge to the latest code, so a caller's old frame still reaches it.
- An edit with errors patches nothing. An edit that changes the layout of values, a type's or a trait's declaration, stops the program and starts it again; compiled code polls a stop flag on entering a function and on each loop's back edge.

## The C back end

`stilt build --release` (`stilt-cli/src/release.rs`) asks the engine for the counted MIR, as a debug build does, then:

1. specializes each instantiation that the roots reach, folding those whose code is the same (`stilt-mir/src/special.rs`);
2. writes it as freestanding C11 with `stilt_codegen_c::emit`, a file for each module and `program.c` for the rest, with the runtime's fast paths in `stilt.h` and the hints a profile gives;
3. compiles the files with clang at `-O2` across the machine's cores, keeping each object in the user's cache under the hash of its C, the clang and the flags (`stilt-cli/src/release/objects.rs`);
4. links the objects with the target's runtime by `rust-lld`, as a debug build does (`stilt-cli/src/link.rs`).

The clang is the one `STILT_CC` names or the toolchain's (`stilt-cli/src/release/compiler.rs`). `STILT_C_DIR` keeps a build's C in a directory, to read it.

## Where to start

- **Build and test.** `cargo build --workspace`, then `just test`, `just conformance` and `just check`; `just ci` before calling a change done. `STILT_DUMP_MIR=1 stilt run main.lt` prints the counted MIR of every function it compiles.
- **A change to the language** starts in the [Reference](../reference/): change the paragraph, add a conformance test that cites it, make the [reference interpreter](../interpreter/) pass it, then the compiler; `just parse`, `just check` and `just run` compare the two.
- **A new diagnostic** is registered in `reference/errors.toml` with the paragraph that defines it, which gives `stilt_diag::codes` its constant; the phase that finds it reports it, a conformance test expects it, and `just snapshots-draft` drafts its rendering in `tests/diagnostics/` for review.
- **A native of the standard library** is declared `= ?` in `std/`, implemented in `stilt-runtime/src/std_*.rs` under the symbol its path gives, as `stilt_std_prelude_str_trim`, and listed in that file's `symbols`, which `stilt_runtime::symbols` gathers; in `stilt-meta/src/natives/` if compile-time code may call it; and in the interpreter, whose `interpreter/lib/std/eval_natives.ml` dispatches each native.
- **A wrong result** is narrowed by the tests of the crate whose output is wrong, in its `src/tests.rs` or `tests/`; the commands' own tests are in `stilt-cli/tests/`.
