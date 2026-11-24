# The Stilt guide

This guide teaches you to write Stilt. Start with the tour, which builds a small arena where creatures fight, then read the chapters in order: each one adds a part of the language, with examples from the same arena. The guide assumes you already know another programming language.

Every program in the guide runs on both the compiler, `stilt`, and the reference interpreter, `stilt-ref`, and the guide's tests check what each one prints.

## Start

| Chapter | What you learn |
| --- | --- |
| [A tour](01-tour.md) | Build the arena in thirty minutes: types, functions, a battle loop, errors, tests, and what the compiler infers |

## The core language

These chapters build on each other. Together they cover `core`, the part of the language every program starts in.

| Chapter | What you learn |
| --- | --- |
| [Values and types](02-values.md) | Numbers, text, lists, maps and tuples, and what copying a value means |
| [Expressions](03-expressions.md) | Blocks, operators, loops, closures and string interpolation |
| [Declaring types](04-declarations.md) | Records, variant types, patterns and `match` |
| [Errors and effects](05-errors.md) | Raising and handling errors, effect rows, panics, and `without` limits |
| [Traits and generics](06-traits.md) | Generic functions, traits and methods |
| [Parameter modes](07-modes.md) | `inout` parameters, and the rule that keeps them safe without references |
| [Programs](08-programs.md) | Modules, packages, tests, examples and properties |
| [The standard library](09-library.md) | Input and output, files, math, time, processes, the network, random numbers and collections |

## The advanced tier

These chapters cover `advanced`, the features a module uses when it needs more control. Each one can be read once you know the core language.

| Chapter | What you learn |
| --- | --- |
| [Views and iterators](11-views.md) | Look into strings and lists without copying them, and iterate lazily |
| [Projections and writing through views](12-projections.md) | Functions that return a place you can assign to |
| [Trait parameters and constructor traits](13-trait-parameters.md) | Traits whose implementations choose a type, and traits over `List` and `Option` alike |
| [Polymorphic arguments and lazy values](14-polymorphism.md) | Arguments that stay generic, and values computed on first use |
| [Records and variadic generics](15-records.md) | Record types written where you use them, and functions over tuples of any length |
| [Pattern macros](16-macros.md) | Add your own syntax with `name!(…)` |
| [Effects, tasks and parallelism](17-effects.md) | Your own effects and handlers, tasks, shared state and parallel loops |

## The meta tier

This chapter covers `meta`, code that runs while the program compiles.

| Chapter | What you learn |
| --- | --- |
| [Value parameters, staging, reflection and procedural macros](18-compile-time.md) | Types that take a number, fixed-size arrays, `comptime`, reflection and procedural macros |

## The design

This chapter can be read on its own.

| Chapter | What you learn |
| --- | --- |
| [Why Stilt is this way](10-design.md) | The principles behind the design, and the alternatives it turned down |

## Everyday tasks

| Page | What you learn |
| --- | --- |
| [Cookbook](cookbook.md) | Short programs for common jobs: files, command-line arguments, JSON, parallel loops and properties |

## Coming from another language

| Page | What you learn |
| --- | --- |
| [Stilt for Rust programmers](for-rust-programmers.md) | Values instead of references, moves the compiler infers, errors in the signature, and the facts it shows |
| [Stilt for Go programmers](for-go-programmers.md) | Errors in the type, variant types, no `nil`, values instead of shared slices, tasks |
| [Stilt for Python programmers](for-python-programmers.md) | Inferred types, errors in the signature, `Option` for `None`, objects as values |
| [Stilt for TypeScript programmers](for-typescript-programmers.md) | Checked unions, exact integers, errors in the type, and no `async` colouring |
| [Stilt for Swift programmers](for-swift-programmers.md) | Value types everywhere, optionals, typed errors, and protocols as traits |

## Run a program

A program is one `.lt` file, a directory that holds `main.lt`, or a package made by `stilt new`. [Programs](08-programs.md) describes all three. To check, run or test one:

```sh
stilt check main.lt
stilt run main.lt
stilt test main.lt
```

`check` reports errors and warnings without running anything. `run` runs the program, and `test` runs its tests. [The command line](../commands.md) lists every command, such as `build` for an executable and `repl` for an interactive session.
