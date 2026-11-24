# The sandbox of compile-time code

*Part of the [design sketch](design-sketch.md), beside [compile-time code](compile-time-code.md). It states what a dependency's compile-time code can do to the machine that checks a program, from what the [Reference](../../reference/16-meta.md) states and the compiler does, and which test holds each boundary.*

## What runs, and where

Two kinds of a package's code take part in checking a program that uses it:

- **Procedural macros** run. A use of one runs the macro's body, and every function it calls, in the compiler's interpreter of typed bodies, `stilt-meta`, inside the process that checks the program ([macros.running](../../reference/16-meta.md#macros.running)). No macro is compiled, and none runs as a process of its own.
- **Pattern macros** run nothing, but their expansions are resolved and checked, and a template that uses macros makes more expansions, so they cost the compiler work.

Staged code runs no code of its own at compile time: `comptime` means what the code without it means, a debug build runs it as ordinary code, and a release build gives the observables of the program without the annotations ([meta.erasure](../../reference/16-meta.md#meta.erasure)). The compiler computes nothing of it while it builds; the C compiler of release builds folds what it can, within its own limits.

The process that checks a program is the command's, or the program's engine, which the language server starts when an editor opens the program's folder. So the threat is a dependency, fetched or a path, whose macros run as soon as someone checks, builds or opens a program that uses them, in a process that holds that user's rights. An engine answers only its user ([engines.private](../../reference/19-tools.md#engines.private)), so a macro's run can't be asked for by another user either.

## What a run can read

- **Its use's parts.** The tokens of the use, split into the parameters' forms ([macros.parts](../../reference/16-meta.md#macros.parts)).
- **The files a use names.** A `meta.File` part is a string literal, written in the code that holds the use, and the compiler, not the macro, reads it: a regular UTF-8 file of the package whose source holds the literal, named by a relative path without `.`, `..`, empty names or names starting with `.`, each matching an entry byte for byte, whose real path, through any link, lies inside the package's directory (E0229, [macros.named-files](../../reference/16-meta.md#macros.named-files)). A dependency's macro therefore reads a file of the user's package only where the user wrote its name, and the file is an input of the program, which an edit expands again.
- **Code.** The typed bodies that the macro reaches, its own module's and those it imports, the standard library's among them, and the shapes of types, as any code reads them ([meta.shapes](../../reference/16-meta.md#meta.shapes)).

Nothing else: no native of `std` that performs `io` has an entry in the interpreter, so neither the file system, the environment, the clock, randomness, the console, the network nor other programs can be reached ([macros.procedural-bodies](../../reference/16-meta.md#macros.procedural-bodies)). The same parts and files give the same expansion on every machine.

## What a run can write

Nothing but its result: an expression, a pattern or a type, which replaces the use and is resolved and checked as code written there ([macros.procedural-uses](../../reference/16-meta.md#macros.procedural-uses)), or a `meta.Error`, reported at a span of the use's parts (E0225). It declares no item. The names its quotes write resolve in the macro's module and its bindings are fresh ([macros.quote-hygiene](../../reference/16-meta.md#macros.quote-hygiene)), so an expansion can't capture or shadow the user's names.

## How it is kept from `io`

- **By checking.** A macro's body, and every function it calls, is checked as a function whose row is empty, or `raise<meta.Error>`: a call that performs `io` is E0502 ([macros.procedural-bodies](../../reference/16-meta.md#macros.procedural-bodies)), whether the call is direct, through a callback given to a parameter that doesn't escape ([effects.inference](../../reference/12-effects.md#effects.inference)), through a trait's method whose row holds `io`, or to the file system. A macro whose module has an error expands no use ([macros.expansion-order](../../reference/16-meta.md#macros.expansion-order)).
- **By the run.** A function whose body has an error, as an impl that performs `io` its trait's row doesn't declare does, panics with `check-error` when the run reaches it ([program.bodies-with-errors](../../reference/04-programs.md#program.bodies-with-errors)), so it never runs, and the use is E0226. A run that reaches C, through a foreign function, a lent pointer or `std.c`, stops (E0226), whatever the manifest grants ([macros.step-limits](../../reference/16-meta.md#macros.step-limits)).

## What a run can allocate, and how long it can run

| Bound | Limit | Past it |
| --- | --- | --- |
| Steps: the macro's own body, each call of a function, a closure or a native, and each turn of a loop | 10,000,000 | E0226, at the use |
| Frames | 10,000 | E0226 |
| Memory: every value the run holds on the heap, texts, lists, maps, tuples, records, variants, closures' captures and code, each with a share for its allocation, and the thread of each fiber that a handler which takes control or a projection runs on | 512 MB | E0226, "it ran out of memory" |
| Expansions nested inside one another, pattern and procedural together | 128 | E0224, at the use the user wrote |
| Tokens of the expansions of a use the user wrote, its own and every nested one | 100,000 | E0231, there |

A use that passes the last two expands no further: nothing more of its expansions is resolved or reported ([macros.expansion-size](../../reference/16-meta.md#macros.expansion-size)), so a macro that uses another twice at each of many levels, or itself twice, costs the compiler at most the work of 100,000 tokens. The bounds are fixed: neither code nor a manifest changes them, so a use fails at the same place in every implementation.

What the bounds leave open is a step's cost. A native that sorts, searches or compares a value of hundreds of megabytes is one step, so a run's time is bounded by its steps times the cost of the largest native over the largest value it can hold, which can be hours. The bound is on the work a run can make the compiler do, not on the wall-clock time, which no implementation could keep the same on every machine.

## What a manifest's grants cover

A manifest grants each dependency its effects and capabilities ([packages.grants](../../reference/04-programs.md#packages.grants)). A grant covers what the dependency's code does when the program runs; a macro's run performs nothing whatever its package is granted, so `may = ["io"]` doesn't let a macro's body print (E0502). What a dependency can't reach beyond its grant:

- **Through compile-time code.** The functions that a template or a quote names are the macro's package's own code, as a call into the package would be, so a quote or a template that names `print`, used anywhere, needs `console` in the dependency's entry (E0608, [macros.expansion-effects](../../reference/16-meta.md#macros.expansion-effects)).
- **Through callbacks.** A function that the caller gives the dependency brings the caller's effects, which need no grant ([packages.own-effects](../../reference/04-programs.md#packages.own-effects)); a closure literal the dependency writes, or a function it names as a value, is its own code.
- **Through traits.** A call through a bound names no impl, so its effects are the caller's; but code that instantiates a bound with a concrete type names that type's impl, so a dependency that gives another package's printing logger to its own generic function uses `console` (E0608, [facts.inference](../../reference/15-facts.md#facts.inference)).

## Where each boundary is held

| Boundary | Code | Tests |
| --- | --- | --- |
| No `io` in a macro's body | `stilt-types` (rows); `stilt-meta/src/natives.rs`, no entry for a native with `io` | `conformance/procedural/declaration_errors.lt`, `conformance/procedural/reaching_io/`, `conformance/packages/granted_macro_run/` |
| Code with errors never runs | `stilt-meta/src/image/walk.rs` | `conformance/procedural/reaching_io/` |
| No C | `stilt-meta/src/natives.rs` | `conformance/foreign/compile_time/` |
| Named files | `stilt-db/src/extras.rs` | `conformance/procedural/file_errors/`, `compiler/stilt-cli/tests/macros.rs` |
| Steps and frames | `stilt-meta/src/limits.rs` | `conformance/procedural/limits/` |
| Memory | `stilt-meta/src/value/weight.rs`, `stilt-meta/src/fiber.rs` | `conformance/procedural/memory/`, `compiler/stilt-meta/src/tests.rs`, `compiler/stilt-meta/src/tests/limits.rs` |
| Nesting and size of expansions | `stilt-hir/src/lower/expand/budget.rs` | `conformance/macros/exponential.lt`, `conformance/macros/expansion_size.lt`, `conformance/procedural/expansion_size/` |
| Grants | `stilt-types/src/packages.rs` | `conformance/macros/ungranted/`, `conformance/packages/ungranted_quote/`, `conformance/packages/ungranted_trait/`, `conformance/packages/callback_effects/`, `conformance/packages/closure_and_value/` |

The reference interpreter holds the same bounds, its memory as the size of its heap, in `interpreter/lib/eval_state.ml`, `interpreter/lib/meta/resolve_macros.ml` and `interpreter/lib/facts/grants.ml`, and the conformance suite runs every test above but the toolchain's against both.
