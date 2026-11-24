# The standard library

These files are the modules of Stilt's standard library, as the [standard library chapter of the Reference](../reference/17-std.md) and [std.natives](../reference/17-std.md#std.natives) define them. Every implementation reads them, so everything written in Stilt here behaves the same in all of them.

| Module | Contents |
| --- | --- |
| `std.prelude` | The prelude ([program.prelude-names](../reference/04-programs.md#program.prelude-names)): `Option`, `Result`, `Ordering` and `Set`, the traits, and the methods of the built-in types |
| `std.io` | `IoError`, standard input, read with or without waiting, writing without a newline, and flushing |
| `std.fs` | Files, their bytes, directories and paths |
| `std.cli` | Command-line arguments and the environment |
| `std.math` | The transcendental functions of `f64` |
| `std.clock` | The system's clocks and waiting, and `Duration`, `Instant` and `DateTime`, with RFC 3339 ([std.durations](../reference/17-std.md#std.durations)) |
| `std.net` | `Stream` and `Listener`, TCP connections and listeners, `Socket` and `Datagram`, UDP, and the addresses of hosts ([std.net](../reference/17-std.md#std.net)) |
| `std.http` | HTTP/1.1 over `std.net`: `Request`, `Response`, a client of `http://` URLs and a server, written in Stilt ([std.http](../reference/17-std.md#std.http)) |
| `std.process` | `Command`, a program to run with its arguments, environment, directory and input; its runs to their end, and `Child`, a program that runs beside the one that started it ([std.process](../reference/17-std.md#std.process)) |
| `std.random` | `Rng`, a generator that a seed reproduces, and entropy |
| `std.collections` | `Deque`, a double-ended queue, and `Heap`, a priority queue |
| `std.encoding` | Base64 and hexadecimal, both ways, and UTF-8 read with the place where it goes wrong ([std.encoding](../reference/17-std.md#std.encoding)) |
| `std.hashing` | SHA-256, its HMAC, and FNV-1a, a fast hash of no cryptographic strength ([std.hashing](../reference/17-std.md#std.hashing)) |
| `std.text` | Unicode's case mappings and properties of characters, on tables of Unicode 17.0.0 ([std.text](../reference/17-std.md#std.text)) |
| `std.regex` | `Regex`, a pattern compiled once and matched in time linear in the text, with groups, replacing and splitting ([std.regex](../reference/17-std.md#std.regex)) |
| `std.view` | `View` and `Iter`: windows into strings and lists, and lazy iterators over them ([views.std-view](../reference/13-modes.md#views.std-view)) |
| `std.lazy` | `Lazy`, a value computed on its first use and kept ([polymorphism.lazy-values](../reference/07-types.md#polymorphism.lazy-values)) |
| `std.array` | `Array<T, n>`, a fixed number of values stored inline ([generics.arrays](../reference/07-types.md#generics.arrays)) |
| `std.meta` | Reflection: a type's shape, its fields and its variants ([meta.std-meta](../reference/16-meta.md#meta.std-meta)); and the tokens, code and cursor of procedural macros ([macros.tokens-and-code](../reference/16-meta.md#macros.tokens-and-code)) |
| `std.json` | JSON values and their text, and any type written as JSON and read back through its shape ([std.json](../reference/17-std.md#std.json)) |
| `std.task` | `Task`, `spawn` and `await`, and the handlers of `async`, `threads` and `sequential` ([tasks.async](../reference/14-tasks.md#tasks.async)), and `Scope` and `scope`, tasks that may raise ([tasks.scopes](../reference/14-tasks.md#tasks.scopes)) |
| `std.sync` | `Shared`, a value that tasks share, reached in `when` ([shared.std-sync](../reference/14-tasks.md#shared.std-sync)) |
| `std.par` | `map`, `each`, `both` and `fold`, whose closures may run on every core ([par.std-par](../reference/14-tasks.md#par.std-par)) |
| `std.c` | `Ptr` and `Str`, the addresses and strings that foreign functions take, and reading and writing through them ([c.module-std-c](../reference/20-builds.md#c.module-std-c)) |

## Built-in types

The types `bool`, `i8` to `u64`, `f32`, `f64`, `str`, `Never`, `List` and `Map` can't be written in Stilt, so they have no declarations. They belong to `std.prelude`, which is therefore their home module, and their `impl` blocks are in `prelude.lt` ([traits.impl-blocks](../reference/11-traits.md#traits.impl-blocks)).

## Native items

A function whose body is `= ?`, and a constant whose value is `?`, is native: each implementation provides it. The reference interpreter implements it in OCaml, and the compiler in its runtime. Everything else is written in Stilt.

## Examples

Every function has at least one `/// ex:` example ([std.examples](../reference/17-std.md#std.examples)). They are the library's own tests: `test --std`, in the reference interpreter and the compiler, runs them, and `just test` runs it in both. No program's `stilt test` runs them, and every other command reads the library without them.
