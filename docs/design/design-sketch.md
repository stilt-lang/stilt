# Stilt: a design sketch for the heaven language

Oct 27, 2026 · @Clément

## Premise

Stilt aims at six of the nine properties people want most from a programming language:

- Go's compile speed;
- Rust's safety;
- C++'s performance;
- for what people want of Lisp's macros, typed and hygienic macros with compile-time code that runs in the editor;
- Haskell's types;
- Elm's error handling.

The other three are libraries, stability and ubiquity. They can't be designed in, so they get bridges instead (see the last sections).

"Elm's error handling" is read two ways here: no runtime exceptions, and compiler errors that teach. Both are targets.

The thesis is that bolting features together fails, but removing the causes of their conflicts can work. Three conflicts matter most:

- optimization vs. compile time;
- expressive types vs. explainable errors;
- macros vs. static analysis.

Each is defused mainly by separating what a program means from how it gets compiled.

Applied to performance, the same separation gives Stilt its character: **values with inferred costs**. Every value behaves as an independent copy. The compiler infers, reports and, on request, guarantees what Rust makes programmers prove by annotation: where values live, where they are updated in place, what may run in parallel, what authority a function holds, and which run-time checks can go. Rust's bargain is to prove aliasing safety by annotation and get speed in return. Stilt's is values by meaning, costs by inference, and guarantees by request. It is "infer, don't declare" applied to performance.

The name is a bird's. A stilt wades through deep water on long legs and stays dry. Stilt keeps a program above memory management in the same way: its code names no lifetimes, and no tracing garbage collector runs.

## Design principles

Six rules hold the design together; every later section is one of them applied.

1. **Meaning is separate from compilation strategy.** Generics, effects, memory management, layout and parallelism each have one semantics and several valid implementations. Debug builds pick the cheapest to compile; release builds pick the fastest to run.
2. **Everything is checkable locally.** Top-level signatures are mandatory, the effects a function performs are written, and failing calls are marked with `try`. Facts inferred from bodies live apart from signatures. Any function can be type-checked, cached and explained without reading the rest of the program.
3. **Every feature pays an error-message tax.** A feature ships only if its common mistakes produce a short explanation pointing at the user's own code. This is Elm's rule, made formal.
4. **Compile-time code is ordinary code, but pure.** It runs the same language in a sandbox, deterministically. Its results are cacheable and visible to the editor, and a release build's specializations mean what the debug build's dictionaries mean.
5. **Power is inferred and shown, per module.** Everyone reads a small core. A module's tier follows from the features it uses: the compiler infers it, the tools show it, and no program declares or limits it.
6. **No hidden costs.**
   - I/O and failure appear in types.
   - Allocation, panics, consumed parameters and the other facts the compiler infers are shown next to every signature, and `without` turns those that code can stay clear of into checked promises.

   Performance and safety can therefore be read from signatures and the facts beside them.

## What you write, what is inferred

A reader needs the types at item boundaries, the effects a function performs (`io` and `raise<E>`), `inout`, and `var` and `try` in bodies. Everything else is a fact the compiler infers, shows and lets you limit. [What you write, what is inferred](inferred-facts.md) gives the rules. Against Rust, the division looks like this:

| Concern | Rust asks the programmer to write | Stilt infers and shows | Stilt checks on request |
| --- | --- | --- | --- |
| Aliasing | lifetimes, `&` and `&mut` | modes, from `inout` and how values are used | exclusivity, always ([modes.law](../../reference/13-modes.md#modes.law)) |
| In-place update | `&mut` plumbing | consumed parameters, uniqueness, Perceus reuse | `without alloc`: in place, no allocation |
| Layout | `Box`, `Vec<Struct>`, `#[repr]` | inline or on the heap | layout control, in the `systems` tier |
| Threads | `Send`, `Sync`, `'static`, `Pin` | thread safety, from modes | determinism (`par`), deadlock freedom (`when`) |
| Authority | nothing | the capabilities below `io` | `without net`, and the like |
| Generic cost | monomorphize everything | dictionaries in debug, every reached instantiation specialized in release | the release build's performance report |
| Run-time checks | trust the optimizer | facts that verification proves | `without panic` |

## At a glance

None of the mechanisms is new; each already works somewhere. What's new is combining them under the six principles.

| Target | Core mechanisms | Borrowed from |
| --- | --- | --- |
| Types (Haskell) | ADTs, traits with higher-kinded types, row-polymorphic effects and records, bidirectional inference, checked compile-time parameters | Haskell, Rust, Koka, PureScript, Mojo |
| Safety (Rust) | Mutable value semantics, inferred modes, views that can't escape, compile-time reference counting, data-race freedom from modes, deadlock-free shared state | Hylo, Swift, OxCaml, Koka, Lean 4, Verona |
| Error handling (Elm) | No null or exceptions; typed failure effects, `try` at call sites, function arguments whose effects pass through, `without panic` | Elm, Koka, Effekt, Swift typed throws, Zig |
| Macros (Lisp) | One staged language: compile-time parameters, reflection as queries, derives as library functions, hygienic macros for syntax only | Mojo, Zig, Racket, Scala 3, Lean 4, MetaOCaml |
| Performance (C++) | No GC, values stored inline, in-place reuse, release builds through C specialized for every instantiation and guided by profiles, refinements that remove checks | C++, Swift, Koka, Lean 4, Flux |
| Compile speed (Go) | One persistent query engine, a fast debug backend that patches running programs, dictionary generics in debug, a shared content-addressed cache | Go, Zig, rust-analyzer, Swift, Unison |
| Error messages (Elm) | Error-message tax, local inference, structured diagnostics with fixes and admissible alternatives, holes that report their context | Elm, Rust, Roc, Hazel |
| Agents | Prefix-decidable checking, a published grammar, path-and-hash edits, one verdict | MoonBit, Hazel, Unison |

The exact rules live in the [Reference](../../reference/), which this sketch follows. Two parts of the sketch have their own pages: [Values with inferred costs](values-and-costs.md) covers memory safety, concurrency and performance, and [Compile-time code](compile-time-code.md) covers the `meta` tier.

## Types (Haskell)

Stilt keeps most of Haskell's type system and drops the two parts that cost the most: global inference and laziness.

**Kept:**

- **Algebraic data types** with exhaustive pattern matching. There is no null; absence is `Option<T>`.
- **Traits (type classes)** with coherence. The `core` tier has traits over a single type, with automatic structural `Eq`, `Ord`, `Hash` and `Show`.
- **Advanced type features.** The `advanced` tier adds:
  - trait parameters, which each impl's type fixes and which serve as associated types, and constructor traits over `Self<A>`, so `Functor` and `Monad` are expressible (Rust can't express these today);
  - anonymous records and record bounds, `P: { name: str, .. }`, so a function takes every record with the fields it needs;
  - variadic generics, packs `..Ts` mapped with `(..e)`, so one `zip` covers any number of lists;
  - polymorphic function types for arguments and fields, so an argument stays generic; polymorphic recursion is already core, since every signature is written.
- **Compile-time parameters.** The `meta` tier makes type and value parameters one mechanism, so types such as `Matrix<f32, 4, 4>` take values ([Compile-time code](compile-time-code.md)).
- **Row polymorphism** for effect rows, in every tier. Most of it never shows, because a function argument's effects pass through to the caller (see Effects).

**Dropped or changed:**

- **Global inference becomes bidirectional checking.** Top-level signatures are required; inference stays local to function bodies. Each function checks independently, in parallel, and errors land on the right line.
- **Laziness becomes opt-in.** Evaluation is strict; `Lazy<T>`, in `std.lazy` (`advanced` tier), exists when wanted, and its function performs no effect, so no program can tell when it runs. This makes performance predictable.
- **No overlapping instances and no open type-level functions** beyond member types, such as `C.Item`. These produce Haskell's worst error messages.
- **Polymorphic recursion and polymorphic arguments can't always be specialized.** The compiler falls back to passing method tables at run time and lists each case in the release build's performance report.

```stilt
type Shape =
  | Circle(radius: f64)
  | Rect(w: f64, h: f64)

fn area(s: Shape) -> f64 {
  match s {
    Circle(r) => f64.PI * r * r
    Rect(w, h) => w * h
  }
}

// Constructor trait (advanced tier): `Self` takes an argument. `f` names
// no effects: whatever it performs passes through to the caller of `fmap`.
trait Functor {
  fn fmap<A, B>(self: Self<A>, f: fn(A) -> B) -> Self<B>
}
```

## Effects and error handling (Elm)

Stilt has no null and no exceptions: every way a function can fail or touch the world is in its type, and every call that can fail is marked.

**Effect rows.** A function's type ends with the effects it performs, after `/`.

- **Built-in effects.** In `core` the effects are `io` and `raise<E>`. User-defined effects and `async` come with the `advanced` tier.
- **No row.** A function without a row performs no explicit effects.
- **Arguments pass their effects through.** A function passed as an argument brings its caller's effects: `fn twice(x: i64, f: fn(i64) -> i64) -> i64` names no row, and `try twice(12, halve)` marks, in the caller, that `halve` can raise. A function parameter may only be called or passed on, unless it is marked `escaping`, as in `fn button(label: str, escaping on_click: fn() / io) -> Button`: a kept parameter's row is exactly the one written, with a row variable where it stays generic. So `map` works with failing callbacks with no effect variable, which removes the "function colouring" problem.
- **Implicit effects.** The implicit effects are `panic`, `overflow` for integer overflow, `alloc`, `div` for possible non-termination, and `copy` for writes that copy shared data. They are inferred, recorded in each module's interface and shown by the tools next to every signature, but never written.

**Failure is a typed effect.** `raise<E>` is checked exceptions done right:

- **Precise error types.** The error type is precise, and a row holds at most one `raise`.
- **Visible control flow.** Every call that can raise sits inside a `try`, as in Swift and Zig. A `try` with a `catch` handles the error; a `try` without one passes it on.
- **No cost on success.** It compiles like Swift's typed throws: the error comes back in a register, with no stack unwinding and no cost on the success path.
- **Errors as data.** `Result<T, E>` stores errors as data. `r.get()` turns an `Err` back into a raise, and `Result.of(|| …)` captures a raise as a value.

```stilt
use std.fs

type Config = { port: u16 }

type ConfigError =
  | Missing(path: str)
  | BadPort(text: str)

fn parse_port(s: str) -> u16 / raise<ConfigError> {
  match s.to_u16() {
    Some(p) => p
    None => raise BadPort(s)
  }
}

fn load(path: str) -> Config / {io, raise<ConfigError>} {
  let text = try fs.read(path) catch _ => raise Missing(path)
  let port = try parse_port(text.trim())
  Config { port }
}
```

**User-defined effects and handlers** (`advanced` tier). Effects are interfaces whose implementation the caller chooses. That one mechanism covers async, generators, dependency injection and test mocks. Handlers resume at most once (as in OCaml 5), which keeps them compatible with the value model, and tail-resumptive handlers, the common case, compile to direct calls.

```stilt
effect Prices {
  fn price(sku: str) -> f64
}

fn total(skus: List<str>) -> f64 / Prices {
  skus.fold(0.0, |sum, s| sum + Prices.price(s))
}

test "totals add prices" {
  let flat = handler Prices { fn price(sku: str) -> f64 { 2.5 } }
  with flat {
    assert total(["a", "b"]) == 5.0
  }
}
```

**Capabilities** (`core` tier). `io` stays the one effect a signature writes for the world. Below it, the compiler infers which capabilities a function uses (files, network, clock, environment, console, randomness, spawning tasks and running programs) and shows them, and `without net` limits one. With the user-defined handlers of the advanced tier, each capability becomes an effect with a handler that `main` installs, so a test can handle `clock` with a fixed time. Signatures don't grow, and a module can still promise that it never opens a socket.

**`async` is an effect** (`advanced` tier) whose handler `main` chooses: threads, or fibers on an event loop, as Zig 0.16 chooses an `Io` in `main`. A function that only does I/O is the same code under every handler, so no library is written in two colours and no executor locks anyone in ([concurrency](values-and-costs.md#concurrency)).

**Panics and `without panic`.** Some operations can still panic: `xs[i]` out of bounds, `m[k]` on a missing key, division by zero, `unreachable()`, integer overflow. The compiler tracks the implicit `panic` effect of every operation except overflow, which would otherwise mark almost all arithmetic, and records it in each module's interface.

A module or a function that says `without panic` must contain no operation that can panic. It uses `xs.get(i)` and `m.get(k)`, which return an `Option`, or indexes that verification has proved in range. That's Elm's "no runtime exceptions" guarantee, applied where you ask for it.

Three failures stay outside `without panic`:

- **Integer overflow.** It still traps at run time; verification inside `check` can prove its absence.
- **Stack overflow and running out of memory.** No systems language can rule these out. Both abort cleanly.
- **Non-termination.** It is the implicit effect `div`, inferred wherever recursion isn't structural or a loop may not end, so `without panic, div` means total.

## Error messages (Elm)

Elm-quality errors are a design constraint, not a polish pass: the error-message tax is enforced by the compiler's own test suite.

- **Errors land where the mistake is.** Mandatory signatures keep inference local, so a type error is reported on the right line, in types the user wrote.
- **Every diagnostic has the same shape:** a code, a plain title, the user's code with labelled spans, a one-paragraph help that says what to do and why, and at most two fixes. Each is snapshot-tested; a change that makes one worse fails CI.
- **Diagnostics are data.** They're emitted as structured records with machine-applicable fixes, so editors and AI agents apply them without parsing prose. Wherever the checker can enumerate them, a record also lists the admissible alternatives: bindings of the expected type, missing variants, effects the row allows, methods with a close name.
- **Features that resist good errors stay out:** overlapping instances, open type-level functions, implicit conversions.
- **Trait failures show the closest candidates,** not the whole search. Errors in compile-time code show the user's code first.
- **Inferred facts explain themselves.** A limit that a fact exceeds names the fact, the line that causes it and the limit, as in "`step` allocates at line 12, where `out.push(y)` may grow `out`; its signature says `without alloc`."
- **Holes report their context.** A `?` checks with a warning, and `stilt show` gives its expected type, the types it mentions, and the headers of functions that fit, in that order.
- **Broken code still runs.** `stilt run` turns a function, test or constant with an error into a `check-error` panic where it is reached, so you can test the rest of the program while fixing it, and exits with status 2 so that nothing mistakes the run for success.

An exclusivity error, written the Stilt way:

```text
── CHANGING A LIST WHILE READING IT ────────────────── src/cart.lt:14:7  [E0404]

You are changing `cart` while a loop is still reading `cart.items`:

  12 │   for item in cart.items {
     │               ────────── the loop reads `cart.items` from here...
  13 │     if item.expired() {
  14 │       cart.remove(item.id)
     │       ^^^^ ...so `cart` can't be changed here.

Changing it mid-loop would silently copy the whole list, and the loop
would keep reading the old items.

To fix it, keep the items that haven't expired:

  12 │   cart.items.retain(|i| !i.expired())
     │   ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
```

Each fix is an edit of the user's code, shown as it reads once applied. An editor or an agent applies it as a path-and-hash edit ([Agent syntax](agent-syntax.md)).

## Compile speed (Go)

Debug builds aim for Go-class speed by doing less work and never redoing it; release builds deliberately spend compile time on runtime speed.

Go is fast on full builds. Stilt bets on the common case instead: rebuilding after a small edit should be close to instant, while clean builds stay acceptable.

- **One engine.** Every step is a cached query keyed by a hash of its inputs, as in rust-analyzer: parsing a file, running compile-time code, checking a function, generating its code. The command line, the language server, agents and running programs share one persistent database. The standard library's inputs are durable, so a body edit never revalidates what depends only on them, and bodies are checked in parallel.
- **Local checking.** Signatures are mandatory, and inferred facts such as implicit effects and consumed parameters live apart from them. So a body change never re-checks its callers, and work spreads across all cores.
- **Generics compiled two ways.**
  - Debug builds compile each generic function once per layout shape and pass a table of trait methods at run time, as Go and Swift do.
  - Release builds specialize every instantiation a program reaches.

  The meaning is identical, so the switch is invisible.
- **Two backends.** Debug runs a cheap optimizer on each function's MIR, then Cranelift, and patches the running program in place. Release emits C and lets the C compiler optimize.
- **No headers, no cyclic imports.** Each module exports a compact interface that dependents compile against, as in Go.
- **Shared cache.** Each function's compiled code is addressed by its body's hash, its callees' signature hashes and the compiler's version, and shared across machines, CI and agents, so a team compiles each definition once (an idea from Unison and Bazel).

```text
Shared front end, every step a cached query:
  parse → run compile-time code → resolve names → check types, modes and exclusivity
        → infer facts and check limits → lower to MIR → optimize MIR → insert reference counting

Debug:    tables per layout shape  → Cranelift         → patch the running program
Release:  specialize each instance → C, PGO            → optimized binary
```

Everything in the front end is shared and cached; only the last steps differ between debug and release.

## Language tiers

Stilt is big, so it is split into tiers, and most application code should live in `core`. Each tier includes the ones above it. A module's tier is the first that allows every feature the module uses: the compiler infers it and the tools show it.

| Tier | Adds | Typical author |
| --- | --- | --- |
| `core` | Values, functions, records and ADTs, pattern matching, single-type traits, generics, `inout`, `io`, `raise` and `try`, function arguments whose effects pass through, inferred consumption and modes; in the library, deterministic `par` | Application developers |
| `advanced` | Views and projections on the inferred modes, `Shared<T>` and `when`, structured `scope`, user-defined effects and one-shot handlers, `async`, trait parameters and constructor traits, polymorphic function types, anonymous records and record bounds, variadic generics, `Lazy<T>`, pattern macros | Library authors |
| `meta` | Compile-time type and value parameters, staging annotations, reflection, procedural macros for syntax | Framework and DSL authors |
| `systems` | `unsafe`, raw pointers, FFI and C header import, inline assembly, layout control and SIMD types, allocator handlers | Runtime and driver authors |

No program names a tier, so none chooses or limits one: a module reaches a later tier by using its features, and stays in an earlier one by not using them.

**`without` limits inferred facts**, on a module or a function. It names the facts the code must stay clear of:

```stilt
module billing.invoice
  without panic

fn step(s: State) -> State without alloc { … }
```

- **Implicit effects.** `without panic` forbids every panic except integer overflow, and `without alloc` forbids allocation, in every tier, and `without div` forbids non-termination.
- **Capabilities and copies.** `without net` forbids a capability, and `without copy` forbids writes that copy shared data.
- **Unsafe code.** `unsafe` blocks and the foreign functions they call are inferred facts, shown next to each signature, which no caller inherits ([c.unsafe-and-foreign](../../reference/20-builds.md#c.unsafe-and-foreign)). `without unsafe` forbids the blocks in a module's or a function's own code, and a package's manifest forbids them in its dependencies unless it grants `unsafe`, as Rust's `#![forbid(unsafe_code)]` and dependency audits do. Keeping such code out is the one reason to limit the `systems` tier, and it belongs to these facts rather than to a tier.

Verification works at any tier. `check` infers range and length facts and proves away the panics they rule out, so code under `without panic` can still index lists.

Tiers bring three benefits:

- They keep code readable.
- They keep `core` errors free of modes and higher-kinded types.
- They keep `core` builds fast, since there is no compile-time code to run.

The idea comes from Racket's teaching languages.

### Words reserved for later tiers

[lexical.reserved-words](../../reference/02-lexical.md#lexical.reserved-words) reserves in `core` every word a later tier needs, so adding a tier never needs an edition. These are the words:

| Word | Tier | What it's for |
| --- | --- | --- |
| `async` | `advanced` | Names the effect that starts and waits for tasks |
| `await` | `advanced` | Waits for a task's result, as the operation of `async`, the way `raise` is the operation of `raise<E>` |
| `effect` | `advanced` | Declares a user-defined effect |
| `handler` | `advanced` | Builds a handler value |
| `resume` | `advanced` | Resumes a one-shot continuation inside a handler |
| `syntax` | `advanced` | Declares a pattern macro |
| `when` | `advanced` | Runs a block once it holds every `Shared<T>` it names, as in `when (a, b) { … }` |
| `where` | `advanced` | States a bound that doesn't fit beside its parameter, on a member type such as `C.Item` or on a compile-time parameter |
| `with` | `advanced` | Handles an effect for the length of a block, as in `with arena(…) { … }` |
| `yield` | `advanced` | Hands the caller a place from a projection, and resumes once the caller is done with it |
| `comptime` | `meta` | Marks an erasable staging annotation, such as `comptime for` and `comptime if` |
| `macro` | `meta` | Declares a procedural macro |
| `quote` | `meta` | Writes a typed quote |
| `extern` | `core`, `systems` | Exports a function to C, as in `pub extern fn`, and in the `systems` tier declares a function or a type from C |
| `unsafe` | `systems` | Marks a block the compiler can't check, with its written justification |

Some words are contextual instead: identifiers everywhere except where the grammar takes the keyword. They are `without` after a module header or a signature, the facts named after it (`panic`, `overflow`, `alloc`, `div`, `copy`, `locks`, and the capabilities `fs`, `net`, `clock`, `env`, `console`, `rand`, `spawn` and `exec`; `unsafe`, already reserved, names the facts of unsafe code there), and `meta` before `use`, which imports a module for compile-time code only.

Other words were weighed and left free:

- **`ref`, `mut`, `move`, `static`.** No tier has first-class references, lifetimes or moves: values are copied, consumption is inferred, and constants are `const`. An agent that writes one out of habit gets a foreign-syntax diagnostic that names Stilt's form (goal `foreign-syntax-named`), which needs no reservation, and `move` and `static` stay free as names.
- **`dyn`.** No tier has trait objects. A value of one of several types is a variant, and a value with behaviour is a record of functions; debug builds already pass method tables, so `dyn` would name a strategy.
- **`own`, `sink`, `local`, `unique`, `once`, `portable`, `contended`.** Modes are inferred and shown, never written ([modes.fact-not-type](../../reference/13-modes.md#modes.fact-not-type)).
- **`scope`, `spawn`, `par`, `Shared`, `arena`, `derive`.** Library names, not keywords: each is a function or a type, and a derive is a reflective library function.
- **`import`.** `use` is Stilt's one import word, and `meta use` covers compile-time imports.

## Scorecard

Stilt gets close on all six, but matches none of the originals exactly. These are design estimates; nothing here is measured beyond what [Goals](goals.md) reports.

| Target | How close | Where it falls short |
| --- | --- | --- |
| Compile speed (Go) | Close for incremental debug builds | Release builds are slower than Go's because optimization costs time. Clean builds of code heavy in compile-time code are slower too. |
| Safety (Rust) | Equal, and easier to write | `unsafe` and FFI remain trust boundaries. Cycles of `Shared<T>` values are freed once nothing else reaches them, by trial deletion of the shared objects alone ([cycles.freeing](../../reference/14-tasks.md#cycles.freeing)). |
| Performance (C++) | Close | Reference counting on heap buffers, the checks verification can't remove, runtime method tables for unspecializable generics. |
| Macros (Lisp) | Equal in power over types, and checked | No reader macros, no runtime `eval`, no live image. Macros cover syntax only; code over types is ordinary compile-time code. |
| Types (Haskell) | Most of it | No global inference, no default laziness, no type families or overlapping instances, no dependent types. |
| Error handling (Elm) | Close under `without panic` | Integer overflow still traps unless verification proves it can't happen. Stack overflow and out-of-memory abort. A much bigger language means more ways to get confused. |

## Bridges to libraries, stability and ubiquity

These three can't be designed, but each can get a head start.

- **Libraries.** C headers are imported directly, as in Zig, with safe wrappers generated where annotations allow, and simple functions cross the C ABI both ways. An embedded-Python bridge allows gradual adoption, like Rust's PyO3 or Mojo. LLM-assisted translation, checked by the compiler and the original test suite, makes porting popular libraries cheaper than ever.
- **Stability.** Rust-style editions.
  - Each package declares an edition.
  - Editions may change syntax and defaults, and code from all editions links together.
  - `stilt migrate` rewrites code automatically.

  This lets the language fix its mistakes without breaking anyone, the paradox Java never solved.
- **Ubiquity.** Native targets (x86-64, ARM64, RISC-V) and, through the C backend, WebAssembly and any platform with a C compiler, as Nim and Lean reach them. With no mandatory runtime, Stilt embeds anywhere C does.

## Open risks

The biggest risk is complexity: every mechanism here works somewhere, but nobody has shipped them together.

- **Learning curve.** Even with tiers, Stilt carries ideas from six languages. Whether `core` stays as small as Go is the open question.
- **Inferred costs fail in their messages.** A language that infers its costs fails where inference disagrees with the programmer, not in its soundness proofs. Mode errors, consumed parameters and capability rows are only as good as their explanations, so each record arrives with approved diagnostic snapshots before compiler code is written.
- **Unproven interactions.** Each of these pairs needs a real design, not just a slogan:
  - effect handlers suspending, or ending their block, while an `inout` access is live;
  - `when` on several `Shared<T>` values combined with the law of exclusivity;
  - reflection invalidating incremental caches when types change.
- **Two backends, one meaning.** Debug code from Cranelift and release code from C must behave identically. Every semantic difference between them is a bug users will hit in production.
- **Implementation cost.** Realistically the full language is a multi-year effort. Compile-speed budgets are measured from the first front end onward, but the claims for compile-time code can only be tested once the `meta` tier exists.
- **Ecosystem cold start.** The bridges help, but a new language still competes with incumbents that AI tools already write fluently.

## The other documents

The documents beside this one cover each part of the design:

- **[What you write, what is inferred](inferred-facts.md):** the division between what a program states and what the compiler infers, the `without` clause, running programs with errors, and the seven commands.
- **[Values with inferred costs](values-and-costs.md):** memory safety, concurrency and performance.
- **[Compile-time code](compile-time-code.md):** the staged `meta` tier.
- **[Goals and measurements](goals.md):** each goal turned into measurable targets, such as edit-to-diagnostics under 25 ms and release speed near Rust's, and how CI enforces them.
- **[Compiler architecture](compiler-architecture.md):** a Rust workspace around one query engine, with Cranelift for debug builds and C output for release.
- **[Agent syntax](agent-syntax.md):** the parts of the syntax and toolchain designed for AI agents, measured at 23% fewer tokens than Python on one program, with edits addressed by path and hash.
