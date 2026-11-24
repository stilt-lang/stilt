# The Stilt Reference

The Reference defines Stilt: what a program means, which programs are rejected and with which diagnostic, and what the toolchain promises of its tools. Every implementation, the reference interpreter and the compiler among them, implements it, and the conformance suite checks it. The [guide](../docs/guide/) teaches the language; the Reference states it rule by rule.

## Chapters

### The text of a program

| # | Chapter | IDs | What it covers |
| --- | --- | --- | --- |
| 1 | [Conformance](01-conformance.md) | `conformance.` | What an implementation is judged on, the command-line protocol, test annotations, and where tests live and run |
| 2 | [Lexical structure](02-lexical.md) | `lexical.` | Source text, comments, identifiers, keywords, literals, tokens and where a newline ends a statement |
| 3 | [Syntax](03-syntax.md) | `syntax.` | The grammar, syntax errors, the canonical format, the tree form and the published grammars |
| 4 | [Programs, modules and packages](04-programs.md) | `program.`, `packages.`, `editions.`, `docs.` | Modules, tiers, imports, the prelude, `main`, exit statuses, tests, packages and their manifests, editions, pinned docs |

### Values and types

| # | Chapter | IDs | What it covers |
| --- | --- | --- | --- |
| 5 | [The value model](05-values.md) | `values.` | Copies, bindings, evaluation order and passing values |
| 6 | [Numbers](06-numbers.md) | `numbers.` | Numeric types, literals, arithmetic, overflow, floats, conversions and printing |
| 7 | [Types and generics](07-types.md) | `types.`, `generics.`, `records.`, `variadics.`, `polymorphism.` | Inference, fields, fields read through `Option`, and the generic forms beyond type parameters |

### Code

| # | Chapter | IDs | What it covers |
| --- | --- | --- | --- |
| 8 | [Expressions](08-expressions.md) | `expressions.` | Blocks, operators, calls, closures, control flow, places and scope |
| 9 | [Patterns](09-patterns.md) | `patterns.` | Pattern forms, bindings, let-else, `match` and exhaustiveness |
| 10 | [Declarations](10-declarations.md) | `declarations.` | Types, functions, constants, holes, namespaces and names |
| 11 | [Traits and methods](11-traits.md) | `traits.` | `impl` blocks, traits, bounds, method resolution, the prelude's traits and trait parameters |

### Effects, modes and facts

| # | Chapter | IDs | What it covers |
| --- | --- | --- | --- |
| 12 | [Effects and handlers](12-effects.md) | `effects.`, `handlers.` | Rows, raising and handling errors, panics, user-defined effects and handlers |
| 13 | [Modes and exclusivity](13-modes.md) | `modes.`, `views.`, `projections.` | Places, exclusive access, inferred modes, views, iterators and projections |
| 14 | [Tasks, shared state and parallelism](14-tasks.md) | `tasks.`, `shared.`, `par.`, `cycles.` | `async`, tasks and scopes, shared values and `when`, `std.par`, and cycles through shared values |
| 15 | [Inferred facts and limits](15-facts.md) | `facts.` | The facts inferred about each function, `without`, capabilities and grants, and verification |

### Compile time and the library

| # | Chapter | IDs | What it covers |
| --- | --- | --- | --- |
| 16 | [Macros, staging and reflection](16-meta.md) | `meta.`, `macros.` | Pattern macros, staging annotations, reflection and procedural macros |
| 17 | [The standard library](17-std.md) | `std.` | The contract of each module of `std` |

### Tools and builds

| # | Chapter | IDs | What it covers |
| --- | --- | --- | --- |
| 18 | [Programs with errors](18-errors.md) | `errors.` | Root-cause diagnostics, reading a file in parts, the error type, phases and where diagnostics are reported |
| 19 | [Properties, edits, the REPL and engines](19-tools.md) | `tests.`, `edits.`, `repl.`, `engines.` | Properties, path-and-hash edits, the REPL, and who an engine answers |
| 20 | [Builds, C and WebAssembly](20-builds.md) | `builds.`, `c.`, `wasm.` | Release builds, profiles, exporting to C, calling C, `unsafe` and the WebAssembly target |
| 21 | [Versions and compatibility](21-versions.md) | `versions.` | A package's API, its versions, how versions are selected, and what each release keeps |

Each chapter has a rationale beside it, in [`rationale/`](rationale/), which says why its rules are what they are and which alternatives they reject. The [glossary](glossary.md) defines the terms that chapters share. [Syntax](03-syntax.md) holds the grammar's productions, and [`grammar/`](grammar/) the GBNF and Lark forms generated from them ([syntax.published-grammars](03-syntax.md#syntax.published-grammars)). [`errors.toml`](errors.toml) is the registry of diagnostic codes, which gives each code its title, tier, phase, primary span and the paragraph that defines it, with the help printed under its diagnostics and examples of its mistake, and [`messages.md`](messages.md) says how the compiler's diagnostics and the registry's help are written. [`c-names.txt`](c-names.txt) lists the names that an exported function may not take ([c.exported-names](20-builds.md#c.exported-names)).

## Paragraph IDs

A chapter is a sequence of **paragraphs**, grouped in sections, each of which states one rule. A paragraph starts with its ID in an anchor on a line of its own, as `<a id="values.independent-copies"></a>`, so that a link to the ID opens the chapter at the paragraph wherever the Markdown is rendered. An ID is the chapter's prefix, a dot, and a few words joined by `-`. A sub-point that is cited on its own has a third segment, as `lexical.commented-out-code.single-token`. An ID is permanent: it always names the same rule, and is never given to another.

Cite a rule by its paragraph's ID. In prose, write the ID, as `values.independent-copies`; in a Markdown document, link it, as [`values.independent-copies`](05-values.md#values.independent-copies). Conformance tests ([conformance.rule-citations](01-conformance.md#conformance.rule-citations)), the registry of codes and the toolchain's sources cite paragraphs the same way.

A paragraph says what holds, in the present tense: "is", "must", "is an error (E0311)". Each diagnostic code that a paragraph gives is named in it, and the registry points each code to its **home**, the paragraph that defines it. A paragraph that defines a feature of the advanced, meta or systems tier says so ([program.tiers](04-programs.md#program.tiers)).

## Examples and tests

Every example of the Reference is a conformance test. A paragraph holds no program of its own: after it, a `Tests:` line links the tests of the suite that cite it, under [`conformance/`](../conformance/). A paragraph that no program can observe, such as one about a tool's output or a build target, says in a `Checked by:` line which of the toolchain's tests check it instead.

The conformance suite is the Reference's executable form. Each test is a program, or a directory of them, whose `//~` annotations state what an implementation must give for it: its diagnostics, its output and exit status, or which of its tests pass ([Conformance](01-conformance.md)). Each test cites the paragraphs it covers, so a paragraph's tests are the programs that show its rule, and a paragraph that no test cites shows up in the coverage report. A rule holds for every program, not only for its tests: an implementation that passes the suite and breaks a paragraph on another program doesn't conform.
