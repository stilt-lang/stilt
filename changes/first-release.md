kind: language

The first release of Stilt, a compiled language whose compiler works out and shows what you don't write down: where each function allocates or copies, whether it can panic, overflow or not end, which capabilities it reaches, and which arguments it uses up. A `without` clause turns any of these facts into a promise that `stilt check` keeps, through every function the code names.

- **The language.** The `core`, `advanced` and `meta` tiers are complete: values counted by reference and updated in place when nothing else holds them, generics and traits, effects and handlers, views, tasks and `std.par`, records and variadics, hygienic macros and compile-time code. Of `systems`, calls into C and functions exported to C. The Reference, in `reference/`, defines all of it, paragraph by paragraph, and its first edition is 2027.
- **Two implementations.** `stilt-ref`, the reference interpreter, and `stilt`, the compiler, agree on the conformance suite and on generated programs. A Lean model proves a core calculus sound and runs the suite's programs as a third implementation.
- **The compiler.** `stilt` checks, runs a program while you edit it, tests it with properties and doc examples, and builds debug executables through Cranelift and release executables through C, for macOS on ARM, Linux on ARM and x86-64, and WebAssembly.
- **Tools.** A formatter, a REPL, a language server with extensions for VS Code and Zed, a tree-sitter grammar, packages from git and local paths, `stilt reduce` for compiler bugs, and a standard library written in Stilt.
- **What it doesn't do yet** is listed in `docs/design/known-limitations.md`.
