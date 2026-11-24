# Compile-time code

*Part of the [design sketch](design-sketch.md). It covers the `meta` tier: compile-time parameters, reflection, derives and macros, and the pattern macros of the `advanced` tier.*

Stilt's compile-time code is as powerful as Lisp's macros for code over types, and it is pure, sandboxed and cached. The `meta` tier folds generics, derives and macros into one staged language. A generic function, a derive and a macro all run the same language at compile time, and each has one meaning, which debug builds compute at run time and release builds compute ahead of it. That is principle 1, "one meaning, several strategies", applied to compile-time code.

## Compile-time parameters

Type parameters and value parameters are one mechanism. Both are compile-time parameters, checked against their bounds before anything instantiates them, as Mojo does. So a generic body that is wrong is reported once, at its definition, in types the user wrote, whether or not anything uses it.

```stilt
use std.array

trait Monoid {
  fn neutral() -> Self
  fn combine(self, other: Self) -> Self
}

// A trait bound and a value parameter are both compile-time parameters.
// The body is checked once, against the bounds, before any use.
fn sum<T: Monoid, n: i64>(xs: array.Array<T, n>) -> T {
  var acc = T.neutral()
  comptime for i in 0..n { acc = acc.combine(xs[i]) }
  acc
}
```

A value parameter has an integer type, `bool` or `char`, and is never written at a call: it is inferred from the arguments' types and the expected type, as a type parameter is, so expressions still take no type arguments. A type argument for one is a literal, a constant or a parameter, as in `Mod<7>`, `Mod<PRIME>` or `Mod<p>`, and never arithmetic. `std.array` gives the fixed-size `Array<T, n>`, stored inline.

- **Debug builds** compile one body. `T`'s table of methods and `n` are hidden run-time arguments, and `comptime for` runs as an ordinary loop. This is the dictionary passing that `core` generics use, extended to values.
- **Release builds** specialize `sum<i64, 4>` and unroll the loop.
- **Staging annotations.** `comptime for`, `comptime if` and `comptime match` annotate the one body a function has; they never add a second one. Each asserts that its range, condition or scrutinee is known at compile time, which the compiler checks, so `comptime for` over a `List` is an error. Their meaning is the erased program's: delete every annotation and the program means the same. The compiler checks the erasure, so no proof falls on the user. Tan and Wei prove when a staged program equals its erased version: once inserting code is typed as an effect, and Stilt already has effect rows to type it ([OOPSLA 2026](https://arxiv.org/abs/2606.30854)). No hint asks for a specialization: a release build specializes every instantiation the program reaches ([builds.no-specialization-hints](../../reference/20-builds.md#builds.no-specialization-hints)).

Lazy, duck-typed comptime, as in Zig, was weighed and rejected. A body is checked only when something instantiates it, so unused code holds errors nobody sees, errors appear at each instantiation, and a language server can't report semantic errors in generic code, which Zig's own author calls one of its fundamental trade-offs ([ZLS #2017](https://github.com/zigtools/zls/issues/2017)). Its branch quota also broke `MultiArrayList` at about 18 fields ([#23352](https://github.com/ziglang/zig/issues/23352)).

## Reflection and derives

Reflection reads a type's shape, an ordinary value: `T.shape()` and `T.name()`, in a module that writes `use std.meta` ([meta.shape-and-name](../../reference/16-meta.md#meta.shape-and-name) and [meta.std-meta](../../reference/16-meta.md#meta.std-meta)). They are no members of every type, so a type may still declare its own `shape` or `name`, which is found first. Each case of a shape gives accessors: an integer type's text, a record's or a tuple's fields, a variant type's cases, a container's elements. No arm refines `T`: the type of a field, an element or a payload is a fresh type of its arm or its loop, which code there passes on to other functions but can't name, so a generic body is still checked once, before anything instantiates it. A field is read through its descriptor, as `f.get(value)`, and `fields.build` makes a value from one call per field. `if T: ToJson { … }` tests whether a type has an impl, and inside the branch `T` has the bound, so a derive uses a type's own impl where it has one.

A function reflects on a type parameter with no bound written: `stilt show` prints `reflects T` among its inferred facts. It sees every field of the type it is given, a private type's too, since a type's fields have the type's visibility and the caller handed the value over. A type without a shape, as a function type, a view or a `Shared`, given to a function that reflects is an error at the call that gives it, naming the chain of functions that reflect.

A derive is a library function that reflects on its type. No type gains an API from compile-time code, and calling one leaves the caller's module in its tier:

```stilt
use std.meta

// Ordinary library code in the meta tier: one function serves every type
pub fn describe<T>(value: T) -> str {
  comptime match T.shape() {
    Int(n) => n.text(value)
    Record(fields) => {
      var parts: List<str> = []
      comptime for f in fields { parts.push("{f.name()}={describe(f.get(value))}") }
      "\{{", ".join(parts)}}"
    }
    _ => T.name()
  }
}

let text = json.to_text(user)   // no derive, no impl block, `User`'s API unchanged
```

- **Debug builds** pass a descriptor of the type at run time, so one compiled `describe` serves every type, and an edit of a type compiles no function that reflects again.
- **Release builds** specialize `describe` per type, which matches what a generated `impl` would do.

Derive macros that generate `impl` blocks were weighed and rejected. A type would gain an API from metaprogramming, the expansion costs compile time (serde's `Deserialize` emits 159 lines for a two-field struct), and agents struggle with macros more than with generics ([Ronacher](https://lucumr.pocoo.org/2026/2/9/a-language-for-agents/)). Scala 3 and Zig made the same choice, and Rust's 2026 reflection goal admits that unspecialized reflection is slower than derives, a gap that release specialization closes.

## Macros for syntax

Macros remain for what compile-time functions can't express: new syntax, such as small sugar and embedded languages.

1. **Pattern macros** (`advanced` tier) for small syntax sugar, hygienic, like Scheme's `syntax-rules`, used as `name!(…)` so every tool parses a use without resolving names ([macros.syntax-declarations](../../reference/16-meta.md#macros.syntax-declarations) and [macros.hygiene](../../reference/16-meta.md#macros.hygiene)).
2. **Procedural macros** (`meta` tier): compile-time functions from syntax to syntax ([macros.procedural-declarations](../../reference/16-meta.md#macros.procedural-declarations) and [macros.quote](../../reference/16-meta.md#macros.quote)). A macro reads its input as tokens, through a cursor written in Stilt, and builds code from quotes, never from strings: `quote { … }` writes an expression, `quote type { … }` a type, `quote pattern { … }` a pattern, and `$` splices a value into one. It produces an expression, a pattern or a type, never an item, so no type gains an API from it. Hygiene is lexical, with no way to break it: a quote's names resolve where it is written, the names it binds are fresh in each expansion, and a name the user sees comes from the user's own tokens. A module that declares macros is imported with `meta use`, so its macros run inside the compiler, and only what their expansions name is linked into the program. A use is marked with `!`, as a pattern macro's is, and its groups may hold any balanced tokens, which the macro reads with no statement terminator at their top level, as inside `( … )`, so an embedded language spans lines freely; a Stilt value enters them as `{e}`, as it enters a string. A macro's errors point at the user's tokens.

```stilt
// Pattern macro
syntax unless {
  ($cond: expr) $body: block => if !($cond) $body
}

unless!(xs.is_empty()) { print(xs[0]) }

// An embedded language, checked at compile time against the file the use
// names. The result's type comes from the schema: a list of anonymous
// records, List<{ name: str, age: i64 }>
meta use sql

let adults = sql!(conn, "db/schema.sql") {
  SELECT name, age FROM users WHERE age >= {min_age}
}
```

## Rules that keep compile-time code from hurting the other goals

- **Pure and deterministic.** Compile-time code performs nothing. A file it reads is named at the use, like the schema above, read by the compiler and handed to it, and becomes part of its cache key; a path outside the package is an error.
- **Run inside the compiler.** Compile-time code runs in the compiler's sandbox, an interpreter of the typed bodies the checker already made, not as a separate program. Builds can't run arbitrary code, closing a supply-chain hole that Rust's procedural macros have, and the editor sees every expansion. A compiler to bytecode, which made Clang's evaluator 28 times faster than its tree walker ([Red Hat](https://developers.redhat.com/articles/2024/10/21/new-constant-expression-interpreter-clang)), comes only if macros' runs show in rebuild times; the compile-time benchmark rebuilds within `compile-time-code-rebuilds` without one.
- **Cached** by a hash of its input and the record of what it read, so a call runs again only when that input changes. Caching compile-time calls gave Mojo a 100x speedup ([Chen](https://www.llvm.org/devmtg/2026-04/slides/quick_talk/quick_talk_chen.pdf)).
- **Budgeted.** Each compile-time call has a fixed budget of 10 million steps, a step being a call or an iteration of a loop, 10,000 frames and 512 MB of memory, which every value it holds counts toward, and the expansions of one use hold at most 100,000 tokens. Neither code nor a manifest changes these, unlike Zig's branch quota. Runaway code fails fast and reports the chain of calls that ran out, at the same call in every implementation. [The sandbox of compile-time code](compile-time-sandbox.md) states what a dependency's macro can read, write, allocate and run.
- **Type-checked output.** Errors point at the user's line first, then show "expanded from…". Macro authors can raise their own diagnostics.
- **No reader macros.** The lexer is fixed, so every tool can always parse every file. Custom syntax lives inside delimited blocks, like the SQL above.
- **Visible.** `stilt show` prints a function as written, and with `--expanded` its macro uses expanded, with `--release` the specializations a release build made.

Lost compared with Lisp: runtime `eval` and image-based live development. `stilt run`, which patches a running program as its files change and works as a REPL without a path, recovers part of that.

## Risks

Prototypes of the tier measured the two risks that the design took, before its records were written.

- **A little dependent typing.** `f.get(value)` has a type that depends on `f`. None is needed: the type of a field, an element or a payload is a fresh type of the arm or the loop that reads it, which code there passes to a generic function but can't name, as an existential type is ([meta.fresh-types](../../reference/16-meta.md#meta.fresh-types)).
- **Debug speed of reflective code.** Debug builds read a type's descriptor at run time. A JSON encoder for a 20-field record written that way took 1.71 times as long as one written by hand under `stilt run`, and 1.51 times as long built, a gap that release builds close by specializing.
