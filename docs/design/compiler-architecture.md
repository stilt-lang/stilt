# Compiler architecture

The compiler is a Rust workspace built around one query database, the engine: every phase is a pure, cached function of its inputs, and the command line, the language server, agents and running programs all share one persistent database. Two back ends hang off a shared middle end: Cranelift for fast debug builds that patch running programs, and C source for release builds, which a pinned clang optimizes. A separate reference interpreter, written in OCaml and sharing no code with the compiler, checks both.

[The guide to the compiler](../../compiler/README.md) walks through its code, and [Compiler internals](compiler-internals.md) gives how it implements each command and feature.

## Architecture

```text
 clients        stilt CLI    language server    agents (check, test --json)    running programs
                     └───────────────┴──────────────────┬───────────────────────────┘
                                                        ▼
 engine         parse → run compile-time code → resolve names → check types, modes and exclusivity
                  → infer facts and check `without` limits → lower to MIR → optimize MIR
                  → insert reference counting → lower effects → generate code
                                                        │
                    ┌───────────────────────────────────┴──────────────────┐
                    ▼                                                      ▼
 back ends     Cranelift (debug, JIT, hot patching)                   C (release, clang, PGO)

 checked by    stilt-ref, the OCaml reference interpreter; every back end is tested against it
```

Every client queries the same database, so a fix that works in the editor also works in CI, and a running program receives each edit as the editor does. Compile-time code that reads types calls back into the type checker through the database. That's why the phases are queries rather than a fixed pipeline.

## The engine

The database lives in an engine: a process that holds one program's database between commands, so that `stilt build` right after `stilt check` runs no front-end query again (goal `one-engine`).

- **Finding it.** An engine listens on a Unix socket named after the program's canonical path and the toolchain's version, beside a lock file it holds for its life, so that no second engine of that version holds the same program. `stilt engine PATH` starts one, and so does the language server, `stilt lsp`, when the editor opens a program that has none.
- **Who it answers.** Only the user who started it ([engines.private](../../reference/19-tools.md#engines.private)), since the engine decides what a command reports and, for `run` and `test`, the code it runs. The socket is in a directory of the user's own under the system's temporary directory, open to no other user, which a command or an engine closes when it finds it open; the socket itself is the user's alone; and each end of a connection checks that the other runs as the same user, through `SO_PEERCRED` on Linux and `getpeereid` on macOS. A command whose directory belongs to another user, or is a link, says so and runs in its own process. Each version of the toolchain has engines of its own, so two versions on one program don't stop each other's ([engines.toolchains](../../reference/19-tools.md#engines.toolchains)).
- **Without it.** `check`, `build`, `run` and `show` on a directory program ask the program's engine, and a command that finds none starts one, in a process group of its own, and waits for it to listen; the engine stops when idle. Commands that start at once start one engine. `test` asks an engine for every program, one of one file included, since the engine keeps what a verdict needs from one submission to the next: the results of tests that can't perform `io`, and the submissions that failed (goal `repeated-failures-flagged`); it runs the tests in its own process, so that a test that overflows its stack ends `test` and not the engine. `check`, `build`, `run` and `show` on a program of one file start no engine and run in the command's own process, with the same code on the same files, so their report is the same either way. A command never talks to an engine of another build of the compiler: each request names the compiler's version and executable, and an engine asked by another build of its version stops, so that the next command starts one of that build.
- **Files.** Before each command the engine takes in the edits made to the program's files since the last, reading again a file whose time of change or size differs, and the whole program when a file is added or removed. The language server sends the text of the editor's open buffers instead, which replace their files' for every client until the editor closes them, so a running program receives each edit as the editor does. An engine that stops while idle takes them with it, and the language server gives the next one every open buffer before it asks.
- **Clients at once.** Taking edits in is the one write to the database, made by one command at a time. Every command then answers from a handle of its own, a snapshot that shares the database's memos, so several answer at once and each meets its latency target while the others run. A write cancels the commands answering, which take the edit in and answer again.
- **Stopping.** An engine stops after two minutes without a command, since it holds the whole program and a pause that long is a break from the work it speeds, unless a session of the REPL is open, or when asked to.
- **Memory.** The cache stays bounded (goal `bounded-cache`). An engine keeps the syntax trees of only the files it read last, since the queries after the parse keep what they need of each tree. A module's resolution is held once: the queries that read it are projections of it, each compared on its own, so no older copy of a module stays beside a newer one. A build keeps the MIR of the functions its entry reaches, and consumption summarizes only those, from the MIR the build keeps, and the engine keeps for the next build the counting and the machine code of only the functions its last build reached. Once a build or a run has lowered its code, the engine keeps the typed bodies of only the bodies it read last: only an edit, which checks the bodies it changes again, or a command that reads a body's types needs one again, while a check keeps them all for the build that follows it. Names are interned, four bytes each, with their text held once for the process, and trees are stored with no spare room in their vectors. What is left is mostly each module's resolution, about 275 MB for the 100K-line project with 30 MB of kept machine code and counting, the same after every replay of the edit script.
- **Release builds.** `stilt build --release` asks the engine as a debug build does, with what it reads of the command's environment, `STILT_CC` and the cache's directory, since the engine's may differ. The engine lowers the counted MIR to C, one file per module and one for the code that no module holds, which `stilt-codegen-c` writes, and clang compiles the files across the machine's cores, each object kept in the user's cache by the hash of its C, the clang and the flags, so that a build after an edit compiles only the files of the modules it changed. The objects link as a debug build's object does, with `rust-lld`, and the executable is the same bytes from any directory and any cache ([builds.release-builds](../../reference/20-builds.md#builds.release-builds) and [builds.same-bytes](../../reference/20-builds.md#builds.same-bytes)). Before it writes the C, the build specializes the counted MIR: each instantiation that the program's roots reach, `main` for an executable and the exported functions for a library, is made from the debug build's code of its function with each witness, dictionary, value parameter and descriptor replaced by what the instance knows, simplified, and folded into another whose code is the same, while the functions of a recursive group that calls itself at a growing type keep their dictionaries, as calls of a polymorphic argument do ([builds.specialization](../../reference/20-builds.md#builds.specialization) and [builds.what-stays-generic](../../reference/20-builds.md#builds.what-stays-generic)). A program's profile, the counts that `run --profile` and `test --profile` add to text kept beside it, is read by its release build, which then holds the program in its own process, marks in the MIR the places the profile counts, and tells clang from the lines whose bodies are as they were which branches are likely and which functions are hot and which cold ([builds.profile-use](../../reference/20-builds.md#builds.profile-use)). `show --release` builds the same release code and reports, for each function, what it costs ([builds.performance-report](../../reference/20-builds.md#builds.performance-report)).
- **Libraries.** `stilt build --lib`, with or without `--release`, builds what the program's exported functions reach, those of its root package written `pub extern fn`, which `stilt-hir` lists with the C types of their signatures ([c.exported-functions](../../reference/20-builds.md#c.exported-functions) and [c.exported-signatures](../../reference/20-builds.md#c.exported-signatures)). The debug back end adds a C function under each one's name, which takes its values as C passes them, makes the runtime ready through `stilt_runtime_once`, calls the compiled function with each value in a word and flushes what the call wrote; the release back end writes the same functions as the end of `program.c`. The objects and every member of the target's runtime library go into one archive, which the CLI writes itself with a table of the symbols each member defines, in GNU's format for ELF and Darwin's for Mach-O, each member with the time 0, the owner 0 and the mode 644, beside a header of C11 and C++ alike.
- **Builds.** The engine keeps from one build to the next each function's reference counting and its machine code, with its relocations and its DWARF, so that a build after an edit counts and compiles only the functions whose code the edit changed (goal `compile-time-code-rebuilds`). A function's code is kept with what its translation asked of the module, such as the static data it declared and the slots it calls through, which a build asks again in the order of the functions, so that it declares everything as compiling every function does and relocates the kept code against the numbers the answers give. A function's DWARF is written once, as it is compiled, and a build puts the pieces of its functions together in one unit, filling in their addresses and offsets. The object and the executable are then those a clean build writes, byte for byte, whatever was kept, and the functions a build compiles are translated apart and compiled across the machine's cores.
- **Running programs.** A program runs in `stilt run`'s process, since it must run there, but its code comes from the engine: `run` receives the program's MIR, each function its entry reaches with its reference counting, and compiles it into its own image. Then, at each look at the program's files, it receives each edit's changed functions, and whether the edit changed the layout of the program's values, so that the program starts again. The front end, the MIR and its counting run once, in the engine, which shares the counting among its runs; `run` only compiles. The MIR travels in postcard's compact binary form: the 100K-line project's is 1.7 MB, which a run reads in 9 ms. With no engine, `run` holds the program in a database of its own and lowers it with the same code, and compiles and patches what it lowers as it does what it receives.
- **The REPL.** `stilt repl` is a session of the REPL on the program in the working directory ([repl.sessions](../../reference/19-tools.md#repl.sessions)). Its front, the database's side, lives in the engine: it checks each input as a test's body of the session's module, with a parameter for each of the session's bindings, of the type it was bound with, lowers it into a function and an entry, and counts them with what they reach of the program, as a run's code is counted. The session's image, in `run`'s process, holds that code and the bindings' values, the words of their layouts, and runs each input's entry on a thread of its own, on a frame of those words, so that a raise or a panic ends only the input. Each answer brings the functions that edits since the last changed, which the image patches as a running program's, and the bindings whose types an edit changed, which the session drops. A session compiles only what its inputs reach, and answers an input of the 100K-line project in about 12 ms at the median (goal `interactive-evaluation`).

Each update of the database is mostly proving that what queries read hasn't changed, so the inputs carry the durability of how often they change: a program file's contents change with each edit, the list of its files when one is added or removed, and the standard library and the files' places never. Bodies are checked in parallel, each thread with a handle of its own, and the diagnostics gathered in the same order as checking them in order, so the output doesn't depend on the number of threads.

## Implementation choices

Write the compiler in Rust and reuse proven components; build only what makes Stilt different.

**Why Rust, given Roc left it?** Roc moved to Zig for faster builds and allocator control, and its creator found the borrow checker guarded against mistakes his team wasn't making ([Corrode interview notes](https://friends.grishka.me/posts/2809053)). Bun moved the other way, to Rust, to eliminate use-after-free and leak bugs ([Bun blog](https://bun.com/blog/bun-in-rust)). For Stilt, two points decide it: agents are fluent in Rust, and Zig's project doesn't accept AI-written code without thorough human review ([Techzine](https://www.techzine.eu/news/devops/142873/bun-switches-from-zig-to-rust-with-claudes-help/)), which matters for upstream fixes. Roc's lessons still apply: many small crates, index-based arenas, and a Cranelift-built compiler for the team's own edit loop. Self-hosting waits until after 1.0; Roc decided not to self-host at all.

| Component | Choice | Why |
| --- | --- | --- |
| Incremental engine | salsa, pinned | Query memoization with fine-grained invalidation and durability levels; it powers rust-analyzer. Pinned because a new version can grow memory, against `bounded-cache` |
| Syntax tree | rowan | Lossless tree that keeps whitespace and comments, needed for the formatter and fix-its |
| Parser | Hand-written recursive descent with Pratt expressions | Best error recovery and messages; generated parsers recover poorly |
| Diagnostics | Own data model and renderer | The model is the product (JSON, fix-its and alternatives); the renderer, a few hundred lines, draws the form of the [design sketch](design-sketch.md#error-messages-elm) |
| Debug back end | Cranelift, after a per-function MIR optimizer | Fast code generation and in-process compilation for hot patching |
| Release back end | Freestanding C11 source, one file per module, compiled in parallel by a pinned clang that `stilt` fetches and checks against a hash the first time a release build needs it, its objects kept by the hash of their C, and linked as debug builds are | Mature optimizers with PGO, every target a C compiler reaches, WebAssembly through clang, and a runtime the C compiler inlines |
| Linker | `rust-lld` for executables, from the toolchain `stilt build` ships; `stilt run` uses the in-process JIT and never links | Linking dominates small rebuilds, and the toolchain needs no SDK |
| Verification | A decision procedure of its own over intervals and differences, a query of each body in the compiler's type checker and a pass of the reference interpreter | Verdicts that a record fixes, so both implementations reach the same ones, which no SMT solver's version and limits allow |
| Formal model | Lean 4 | Proofs about the `core` rules, plus a language with strong macros to learn from |
| Fuzzing | cargo-fuzz plus a custom program generator | Coverage-guided parser fuzzing; generated programs for the back ends |

LLVM IR, through inkwell, was weighed as the release back end and kept as the fallback. It gives precise integer semantics and guaranteed tail calls directly, but the runtime would have to ship as bitcode to be inlined, and Lean's LLVM back end lost to its own C back end on exactly that point ([lean4 #3192](https://github.com/leanprover/lean4/issues/3192)). The C back end emits checked builtins for overflow, unsigned arithmetic for wrapping operators, a check of each shift's amount and of each divisor, including `MIN / -1`, compiles with `-fwrapv -fno-strict-aliasing -ffp-contract=off -fno-math-errno`, so no multiply and add fuse, probes each page of a large frame, so a stack overflow still faults in the guard page, and keeps `#line` directives. An LLVM back end is built only if C output misses `release-speed`, which it meets: the benchmark suite's release builds run at 1.07 times their Rust baselines' cycles, as a geometric mean, the slowest, json, at 1.60. MLIR, copy-and-patch and e-graphs on the main path were rejected: their returns are small or negative for Stilt's goals, and their compile-time costs conflict with `edit-to-diagnostics` and `edit-to-running-program`.

## Repository layout

One crate per phase keeps the compiler's own rebuilds fast and each part small enough to read whole.

```text
stilt/
├── reference/                # the Reference: its chapters, rationale, published grammars, errors.toml
├── conformance/              # the conformance suite (tests with //~ annotations)
├── std/                      # standard library, written in Stilt
├── interpreter/              # stilt-ref, the OCaml reference interpreter
├── compiler/
│   ├── stilt-syntax/        # lexer, parser, lossless tree
│   ├── stilt-fmt/           # the formatter, on the lossless tree
│   ├── stilt-edit/          # a module's parts, their paths and hashes, and the edits that replace them
│   ├── stilt-db/            # query database and inputs, with their durability
│   ├── stilt-hir/           # name resolution, module graph, HIR
│   ├── stilt-meta/          # the compile-time interpreter, reflection queries, macro expansion and hygiene
│   ├── stilt-types/         # bidirectional checker, traits, effect rows, modes, exclusivity, inferred facts, verification
│   ├── stilt-mir/           # MIR, lowering, layout of values, the per-function optimizer, specialization
│   ├── stilt-rc/            # Perceus insertion and reuse
│   ├── stilt-codegen-clif/  # debug back end and hot patching
│   ├── stilt-codegen-c/     # release back end
│   ├── stilt-runtime/       # reference counting, panics, tasks, entry point
│   ├── stilt-diag/          # diagnostics model, renderers, fixes and alternatives
│   ├── stilt-pkg/           # manifests, the package graph, fetched dependencies
│   ├── stilt-lsp/           # language server
│   └── stilt-cli/           # check, run, test, build, show, fmt, the engine and the REPL
├── tools/
│   ├── runner/               # stilt-test, the conformance runner; drives any implementation
│   ├── generator/            # stilt-gen, program generators for differential testing
│   ├── grammar/              # the generator of the published grammars
│   ├── latency/              # the latency and memory harness
│   ├── fuzz/                 # fuzz targets
│   ├── linux/                # the Linux machine of the Docker recipes
│   └── measurements/         # studies, such as the token cost of programs
├── tests/                    # diagnostics snapshots, formatter pairs, and the facts, holes, alternatives and costs suites
├── bench/                    # the benchmark suite, its Rust baselines, and the compile-time benchmark
├── examples/                 # programs written in Stilt
├── editors/                  # the VS Code extension
├── formal/                   # Lean 4 model of core typing and modes
└── docs/                     # the guide and the design documents
```

CI rejects any import cycle between crates. Calls that would otherwise form a cycle, such as compile-time code that reflects on types, go through the query database instead. Bun's port hit about 16,000 compiler errors once cyclic dependencies were untangled ([Bun blog](https://bun.com/blog/bun-in-rust)); Stilt avoids that by never allowing them.

## Core data structures in code

Four structures carry the design: the queries, the arenas, the types with their effect rows, and the diagnostics. These are sketches in salsa style; exact library APIs vary by version.

**Queries.** Declarations, bodies and inferred facts are separate queries, so editing a body never invalidates the type checking of its callers. This is where mandatory signatures pay off. The standard library's inputs are durable, so a body edit never revalidates queries that depend only on them, and `infer_body` runs in parallel across bodies.

```rust
#[salsa::input]
pub struct SourceFile {
    #[returns(ref)] pub text: String,
    pub path: PathBuf,
}

#[salsa::tracked]
pub fn parse(db: &dyn Db, file: SourceFile) -> Parse { /* lossless tree */ }

#[salsa::tracked]
pub fn declarations(db: &dyn Db, program: Program) -> Declarations {
    // Every signature, from the declarations only, without positions.
}

#[salsa::tracked]
pub fn infer_body(db: &dyn Db, body: BodyId) -> Inference {
    // Reads callee *signatures*, never callee bodies.
}

#[salsa::tracked]
pub fn facts(db: &dyn Db, body: BodyId) -> Facts {
    // Consumed parameters, `panic` and `alloc`, and the features used;
    // read by the `without` limits, code generation and `show`, never by type checking.
}
```

**Arenas, not pointers.** Every node is a 32-bit index into an arena, as in Roc's and Zig's compilers. Data stays compact, cache-friendly and trivially serializable for the shared cache.

```rust
#[derive(Copy, Clone, PartialEq, Eq, Hash)]
pub struct ExprId(u32);

pub struct Body {
    pub exprs: Arena<ExprId, Expr>,
    pub pats:  Arena<PatId, Pat>,
    pub spans: ArenaMap<ExprId, Span>,   // kept apart so edits that only move code stay cheap
}
```

**Types with parameter modes and effect rows.** The written mode and the row are part of every function type, so the checker, the passes after it and the back ends all read the same facts. Whether a parameter is consumed is not: it lives in `Facts`, apart from the type.

```rust
pub enum Mode { Let, Inout }

pub struct FnTy {
    pub params:  Vec<(Mode, Ty)>,
    pub ret:     Ty,
    pub effects: EffectRow,
}

pub struct EffectRow {
    pub known: SmallVec<[Effect; 4]>,   // io, raise<E>, user-defined effects
    pub tail:  Option<RowVar>,          // only on a function parameter that is kept
}

pub enum Ty { Con(TyCon, Vec<Ty>), Var(TyVar), Fn(Box<FnTy>), /* ... */ }
```

**Diagnostics as data.** The renderer for humans and the JSON for agents come from the same record, and every fix is a concrete edit: the model holds spans of the file, and the JSON gives each as an edit of the part that holds it, the part's address with its hash and its whole new text, which `stilt check --edit` applies as it is ([edits.json-form](../../reference/19-tools.md#edits.json-form) and [edits.fixes-as-edits](../../reference/19-tools.md#edits.fixes-as-edits)). A diagnostic offers a fix only when the compiler knows the whole correction, and the renderer shows each fix as rustc shows a suggestion: the lines it changes as they read once it is applied, with `+` under inserted text and `~` under replaced text, or as they read before, with `-` under what it deletes. A failed lookup offers the closest names as fixes, and a mismatch of two types shows only the parts that differ ([Goals](goals.md), `closest-candidates` and `mismatch-diffs`). Where the checker can enumerate them, a diagnostic also lists the admissible alternatives (`admissible-alternatives`): for a mismatch, the bindings in scope of the expected type; for a `match`, the values its arms miss; for an effect, what the row holds; and for a failed lookup, the names, fields or members close to the one written. Each is `{kind, text}`, with a binding's `type`, and the rendering for people leaves them out, since its message stays short (`short-messages`). A code is a constant built from `reference/errors.toml`, so a diagnostic can only carry a registered code, and its title and one-paragraph reason come from the registry's entry. Serialized whole, a record looks like the JSON below: first the fields that [conformance.diagnostic-objects](../../reference/01-conformance.md#conformance.diagnostic-objects) requires, then the rest. The verdict of `stilt test --json` flattens it into the [conformance.diagnostic-objects](../../reference/01-conformance.md#conformance.diagnostic-objects) fields, plus the path-and-hash fields described in [Agent syntax](agent-syntax.md): `at`, the address of the part that holds its primary span ([edits.diagnostic-addresses](../../reference/19-tools.md#edits.diagnostic-addresses)).

```rust
pub struct Diagnostic {
    pub code:         Code,             // E0404, with its title and reason in the registry
    pub range:        TextRange,        // the primary span, in bytes of its file
    pub message:      String,           // one short sentence
    pub label:        Option<String>,   // what the primary span shows
    pub notes:        Vec<Label>,       // other spans, each with what it shows
    pub fixes:        Vec<Fix>,         // at most two; each a list of text edits
    pub alternatives: Vec<Alternative>, // what would fit here, at most 10
}
```

```json
{"code": "E0404", "file": "src/cart.lt", "line": 14, "col": 7,
 "at": "cart.prune/body#91ad",
 "message": "you are changing `cart` while a loop is still reading `cart.items`",
 "title": "changing a list while reading it",
 "labels": [{"range": [[14, 7], [14, 11]], "text": "...so `cart` can't be changed here", "primary": true},
            {"range": [[12, 15], [12, 25]], "text": "the loop reads `cart.items` from here...", "primary": false}],
 "fixes": [{"title": "use retain",
            "edits": [{"at": "cart.prune/body#91ad", "new": "{ cart.items.retain(|i| !i.expired()) }"}]}],
 "alternatives": []}
```

A type mismatch adds `chain`, the steps that gave each side its type, each a span and what it gave, the last at the mismatch: `[{"range": [[6, 7], [6, 8]], "text": "`n` is bound here, with the type `i64`"}, {"range": [[7, 16], [7, 17]], "text": "here `i64` is found where `str` is expected"}]`.

## How each feature is implemented

Every feature maps to a known algorithm with a reference implementation to study; the new work is making them share one middle end.

| Feature | How it's built | Study first |
| --- | --- | --- |
| Parsing and recovery | Recursive descent with Pratt expressions; on error, skip to a synchronizing token and keep a partial tree so later phases still run | rust-analyzer's parser |
| Type checking | Bidirectional: check against known types, infer only inside bodies; unification variables never escape a function. Every error is marked where it is, and checking continues around it | Dunfield and Krishnaswami, "Complete and Easy Bidirectional Typechecking"; Hazel's marked lambda calculus |
| Prefix checking | A body cut off at any token is sealed by a hole and closed braces, then checked; the hole reports the expected type and the admissible next tokens | Mündler et al., type-constrained decoding |
| Traits and higher-kinded types | Coherent instances, orphan rules, kind checking; a trait solver that returns the closest candidates on failure | Rust's next-generation trait solver; GHC |
| Effect rows | Row polymorphism over sets of labels, with at most one `raise<E>` per row in `core`; a function parameter that is only called or passed on passes its effects to the caller, and scoped labels arrive with user-defined handlers | Koka; Effekt's second-class blocks; Leijen, "Extensible records with scoped labels" |
| Modes | On typed bodies, check the law of exclusivity with lexical access durations ([modes.law](../../reference/13-modes.md#modes.law) and [modes.durations](../../reference/13-modes.md#modes.durations)). Consumption is inferred per function, solved together for recursive functions. Locality, uniqueness, once, portability and contention are inferred on a lattice, as facts apart from the signatures ([modes.fact-not-type](../../reference/13-modes.md#modes.fact-not-type)) | Hylo; Swift's exclusivity enforcement; OxCaml's modes; Lean 4's borrow inference |
| Views and projections | Views that can't escape, whose dependence on a parameter is inferred from the signature, as a pointer and two offsets kept alive by exclusivity ([views.escaping](../../reference/13-modes.md#views.escaping) and [views.across-calls](../../reference/13-modes.md#views.across-calls)); lazy iterators inlined into their consumer; projections lowered as calls that `yield` a place | Hylo subscripts; Swift's non-escapable types |
| Values stored inline | Fixed-size records and variants kept in registers and in place in fields and lists; an `inout` access makes its value unique once | Swift; OxCaml's unboxed types; Lobster |
| Reference counting | Insert `dup`/`drop` from ownership, infer borrowed parameters, reuse a uniquely owned cell in place; counts atomic only behind a shared bit | Koka's Perceus; Lean 4's "Counting Immutable Beans"; biased reference counting |
| MIR optimizer | Scalar replacement of aggregates, promotion to registers, `std` inlined into user functions, generics compiled once per layout shape; nothing crosses a user function's boundary | Go's and Carbon's shapes; Swift's value witness tables; Wasmtime's inliner |
| Effect handlers | Evidence passing: each stack keeps the handlers installed on it, which a `with` extends and a performance searches by effect; a handler that resumes at once is a direct call, a body that ends its `with` returns a tagged value to it as a raise does, and a body that resumes runs on a stack of its own, switched to and back, never copied; on WebAssembly, whose code can't switch stacks, binaryen's Asyncify unwinds the body's frames into memory and rewinds them, in the functions that hold them alone | Xie and Leijen, "Generalized Evidence Passing"; Lexa; OCaml 5; binaryen's Asyncify |
| `raise` and `try` | Lowered to a tagged return value, error in a register, no unwinding | Swift typed throws |
| Tasks | `task.threads()` runs each task on a thread of a pool with a deep copy of what it captures; the output kept as a tree of segments, one per task inserted at its `spawn`, written out in order as each ends, and reads, panics and exits waiting for their segment's turn; a scope's tasks run ahead of their raises, and what follows the first is cancelled ([tasks.same-output-under-every-handler](../../reference/14-tasks.md#tasks.same-output-under-every-handler); [tasks.scope-failure](../../reference/14-tasks.md#tasks.scope-failure)) | Cilk's reducer hyperobjects, which give output in the serial order |
| Parallelism and `when` | `std.par` in chunks on a pool of threads, by heartbeat scheduling in release builds, a fold combining over the tree its list's length fixes; `Shared<T>` as cowns, a `when` holding every cown it names at once, after every task before it in the order of the sequential run that holds a cown or may raise has ended, so the blocks of one cown run in that order ([shared.when-order](../../reference/14-tasks.md#shared.when-order); [par.sequential-meaning](../../reference/14-tasks.md#par.sequential-meaning)) | Westrick et al., heartbeat scheduling; behaviour-oriented concurrency |
| Compile-time code | An interpreter of typed bodies run in a sandbox with a step budget, cached by its input and the reflection queries it read; sets-of-scopes hygiene over the uniform syntax tree | Mojo; Racket (Flatt, "Binding as Sets of Scopes"); Clang's bytecode interpreter; Lean 4 |
| Reflection | Debug: a descriptor of each reflected type passed beside its witness, the descriptors of its parts made by thunks, so a recursive type's is cyclic; a function that reflects compiled once for every type it reflects on, holding that type's values in one word, which a call gives a value of several words in its box; a bound test reads the descriptor's table of impls, where the structural impl of a tuple, a record, a variant type or an array is code shared by every type of its shape, walking the value's parts through the descriptor, so an edit of a type compiles no function again but its descriptor's and its accessors'. Release: specialized, as generics are | Swift's value witness tables and type metadata; Go's `reflect` |
| Generics | Debug: one copy per layout shape plus a method table. Release: specialize every instantiation a program reaches, folding those whose code is the same; only polymorphic recursion and polymorphic arguments keep the table, and the release build's performance report lists them | Swift witness tables; Go dictionaries |
| Release builds | The counted MIR as freestanding C, the runtime's fast paths a header that clang inlines; a function that no other file names is `static`; a list's length and elements kept in C locals across the stores to its elements, by a forward analysis over each function's blocks; a list that a `var` takes new, or that a loop writes in every iteration, made unique once, in every build | Lean 4's and Koka's C back ends |
| Hot patching | Debug builds call through a function table; a rebuilt function swaps its entry in the running process. A layout change restarts the program and migrates the values whose migration is obvious | Zig incremental compilation; Erlang's `code_change` |
| Verification | Six rules of acceptance, each a shape of code with a name, as a range loop or a guard, read from each typed body's text: each check they prove discharges a panic, which `without panic` then accepts, and each counting loop and each self-call that shrinks a `div`, which `without div` accepts, and an operation that none proves gets an error naming what the closest rule needs. Beside them, abstract interpretation of each typed body over the differences between its integers, lengths and versions, widened to the numbers of the body, proves more checks, for release builds alone ([facts.verification](../../reference/15-facts.md#facts.verification)). Lowering marks the location word of each proved operation, and a release build drops the checks its marks name, as conditions clang takes as false; a debug build reads no mark and keeps every check, and the reference interpreter, which reads the six rules alone, keeps every check too, so a wrong proof shows as a difference from the reference interpreter | Miné, the zone and octagon domains; Logozzo and Fähndrich, Pentagons |

Paper titles in this table are cited from background knowledge rather than looked up for this doc; check them before relying on details.
