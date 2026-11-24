# Reference interpreter

`stilt-ref` defines the observable behaviour of Stilt programs, and every other implementation is tested against it. It is written in OCaml 5, as simply as the [Reference](../reference/) allows: obviously correct beats fast. It shares no code with the compiler.

| Path | Contents |
| --- | --- |
| `lib/` | The interpreter: at its root the stages that run in turn and the trees they pass on; below it, a directory for each chapter of the Reference that holds the modules implementing it, from every stage (below). Every module has an `.mli` that documents what it exports, but `lexical/token_type.ml`, which holds only the type of tokens, and `lexical/lexicon.ml`, which `just grammar-generate` writes from the Reference |
| `bin/` | The command line, which follows the protocol of [conformance.commands](../reference/01-conformance.md#conformance.commands) and [conformance.observables](../reference/01-conformance.md#conformance.observables) |
| `gen/` | Embeds the [standard library](../std/)'s sources in the binary, and its trees, parsed and checked when the binary is built, so that a command doesn't parse the library again |
| `test/` | Unit tests, written with `ppx_expect` |

## From text to what it reports

`lib/driver.mli` runs these in order:

1. **Lexing and parsing**: each file into an `Ast`, read a part at a time after a syntax error (errors.parts). The grammar is `lib/parser.mly` and the `parser_*.mly` files beside it, one for each section of [the syntax chapter](../reference/03-syntax.md).
2. **Name resolution** (`lib/resolve.mli`): what every name refers to, as a `Hir`. A use of a procedural macro asks the driver, through `procs`, which checks the macro's module and runs the macro with the evaluator.
3. **Type checking** (`lib/check.mli`, over the signatures of `lib/env.mli`): each body on its own, elaborated into a `Tast`.
4. **The checks after it** (`lib/phases.mli`), in the phases of [errors.phases](../reference/18-errors.md#errors.phases): marking, exhaustiveness, exclusivity, views, the inferred facts with the `without` limits, and the rules of acceptance; then the grants of dependencies.
5. **Evaluation** (`lib/eval.mli`): a tree-walking evaluator of the typed program.

Each stage's work on a part of the language lies in the directory of the chapter that defines that part, so that a question about a paragraph is settled in one directory: `lib/patterns/` holds the resolution of patterns, their checking, the exhaustiveness check and their matching when the program runs.

| Directory of `lib/` | Chapter | What its modules do |
| --- | --- | --- |
| `conformance/` | [1](../reference/01-conformance.md) | The JSON of the command-line protocol |
| `lexical/` | [2](../reference/02-lexical.md) | The lexer, the table of words and tokens, and the tokens |
| `syntax/` | [3](../reference/03-syntax.md) | The tree of the syntax, the parser's driver, reading past syntax errors, and the tree form that `parse --sexp` prints |
| `programs/` | [4](../reference/04-programs.md) | Programs, modules and their paths, packages and manifests, and bodies with errors |
| `values/` | [5](../reference/05-values.md) | The values of a run, and strings |
| `numbers/` | [6](../reference/06-numbers.md) | Integers, floats, literals and the arithmetic operators |
| `types/` | [7](../reference/07-types.md) | Types, their inference, records, spreads, arrays, generics and value parameters |
| `expressions/` | [8](../reference/08-expressions.md) | Expressions, blocks, calls, closures, branches and loops |
| `patterns/` | [9](../reference/09-patterns.md) | Patterns, refutability, exhaustiveness and matching |
| `declarations/` | [10](../reference/10-declarations.md) | Items, constants, bodies and scopes |
| `traits/` | [11](../reference/11-traits.md) | Traits, impls, methods and the dispatch of calls |
| `effects/` | [12](../reference/12-effects.md) | Effect rows, marking, handlers and resumption, and escaping parameters |
| `modes/` | [13](../reference/13-modes.md) | Modes, copies, exclusivity, views, projections and iterators |
| `tasks/` | [14](../reference/14-tasks.md) | Tasks, `when` and parallel functions |
| `facts/` | [15](../reference/15-facts.md) | The inferred facts, the `without` limits, the rules of acceptance, capabilities and grants |
| `meta/` | [16](../reference/16-meta.md) | Macros, quotes, staging and reflection |
| `std/` | [17](../reference/17-std.md) | The natives of the standard library, files, processes, the network and formatting |
| `errors/` | [18](../reference/18-errors.md) | Diagnostics |
| `tools/` | [19](../reference/19-tools.md) | Property tests, the comparison of doc bodies, and `model`, which writes a program as the Lean model's calculus writes it ([formal/README.md](../formal/README.md#executable-semantics)) |
| `builds/` | [20](../reference/20-builds.md) | Foreign functions and exported names |

A change to the language is made here first, once the Reference states it: the conformance test that cites the paragraph passes against this interpreter before the compiler implements it.

## Building and testing

Build it and run its unit tests in the repository's local opam switch:

```sh
opam exec --switch=. -- dune build
opam exec --switch=. -- dune test
```

`just conformance` runs the [conformance suite](../conformance/) against it. Beside the commands of the protocol, `stilt-ref model PROGRAM` writes a program without errors as JSON in the Lean model's calculus, or ends with status 125 when the program uses something the calculus lacks, which it names, so that the model runs the suite's programs too ([formal/README.md](../formal/README.md#executable-semantics)).

It calls C through libffi ([c.both-implementations](../reference/20-builds.md#c.both-implementations)), from stubs of its own (`lib/foreign_stubs.c`), the one C library it links: macOS's SDK holds it, and Linux's `libffi-dev` gives it. A lent list is copied into a C buffer, and back into the list after `with_mut_ptr`'s closure returns.

It reads a package's manifest and its path dependencies ([packages.manifest](../reference/04-programs.md#packages.manifest) and [packages.path-dependencies](../reference/04-programs.md#packages.path-dependencies)), which are all that conformance tests hold, since none reaches the network. A manifest that names a fetched dependency is a program it doesn't take: fetching, versions and their selection are the compiler's alone, and its own tests check them with git repositories they make.

What `without panic` and `without div` accept, it decides by the six rules of acceptance of [facts.rules-of-acceptance](../reference/15-facts.md#facts.rules-of-acceptance) alone, a range loop, a guard, a divisor, a key, a counting loop and shrinking recursion, each read from a body's text (`lib/facts/accept*.ml`), and it keeps every check when it runs. The analysis that proves more checks is the compiler's, and only speeds its release builds, so a wrong proof shows as a difference between a release build and the interpreter.
