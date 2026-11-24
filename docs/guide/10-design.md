# Why Stilt is this way

Copying a creature gives you a second creature, which changes on its own:

```stilt
type Element = | Fire | Water | Plant

type Creature = { name: str, element: Element, hp: i64, attack: i64 }

fn main() / io {
  let embercat = Creature { name: "Embercat", element: Fire, hp: 30, attack: 8 }
  var fainted = embercat
  fainted.hp = 0
  print("{embercat.name} has {embercat.hp} HP, its copy {fainted.hp}.")
}
```

```output
Embercat has 30 HP, its copy 0.
```

Setting `fainted.hp` leaves `embercat` at 30 HP. In Rust, `let mut fainted = embercat` would move the creature, and reading `embercat` after it would be an error. In Python or Java, the two names would share one creature, and both would show 0. In Stilt every value is an independent copy. Making that cheap is the compiler's job: it shares a string, a list or a map between copies, and copies it only when one of them is written while shared ([how copies stay cheap](../../reference/rationale/05-values.md#value-semantics)).

That split, one meaning for a program and several ways to compile it, runs through the whole design. Each section of this page takes one part of the language and says what Stilt chose, what other languages chose, and what each choice costs. The [Reference](../../reference/) states the rules, and the [rationale](../../reference/rationale/) of each of its chapters gives the full argument.

## The six principles

Every decision on this page applies at least one of these principles, from the [design sketch](../design/design-sketch.md):

1. **A program means one thing, however it is compiled.** Every construct is defined by what a program can observe ([conformance.observables](../../reference/01-conformance.md#conformance.observables)), and how it is compiled is left to the implementation. No meaning differs between builds, which is why integer overflow stops the program in release builds too.
2. **Every function can be checked on its own.** Signatures are written in full: parameter types, the return type and the effect row. Types are inferred inside a body, from the signatures it uses, never from another body ([types.inferred-per-body](../../reference/07-types.md#types.inferred-per-body)). What the compiler infers from a body, such as whether it can panic, is kept out of the signature ([facts.interfaces](../../reference/15-facts.md#facts.interfaces)), so editing a body never type-checks its callers again.
3. **Every feature pays for its error messages.** A feature goes in only if its common mistakes get a short message that points at your code. Every diagnostic has a code, a title, a fix and examples in [the registry](../../reference/errors.toml), and only root causes are reported ([errors.root-causes](../../reference/18-errors.md#errors.root-causes)). Type aliases, implicit conversions, row-polymorphic records and variadic generics stay out of `core` for this reason.
4. **Code that runs at compile time is ordinary code, and pure.** Procedural macros are written in Stilt and run in the compiler, deterministically and within a budget of steps. The lexer is fixed, so every tool can parse every file ([lexical.tokens](../../reference/02-lexical.md#lexical.tokens)). Equality, ordering, hashing and printing come with every data type ([traits.structural-impls](../../reference/11-traits.md#traits.structural-impls)), so `core` needs no `derive`.
5. **Power is inferred and shown, per module.** A module's tier is the first of `core`, `advanced`, `meta` and `systems` that allows every feature it uses ([program.module-tier](../../reference/04-programs.md#program.module-tier)). No program names, chooses or limits a tier, and the tools show it. Errors in `core` code never mention lifetimes or higher-kinded types.
6. **No hidden costs.** Input, output and failure are in a function's type, and the tools show where it allocates and can panic. A loop that changes the list it reads, which would copy the list silently, is an error. Any other write to shared data copies it without a diagnostic ([values.independent-copies](../../reference/05-values.md#values.independent-copies)).

The [Agent syntax](../design/agent-syntax.md) document adds two rules for code that agents write. *Count tokens per solved task*: keywords come from languages models already know. Six constructs save tokens where agents spend them: let-else, the `else` fallback, key paths, field punning, one-line blocks and `/// ex:` examples. *Every name has exactly one home*: no overloading, no re-exports and no import aliases, so grep finds every definition, and each one has a unique path.

## The goal

Stilt aims at six properties that programmers usually find in six different languages: Go's compile speed, Rust's safety, C++'s performance, Haskell's types, Elm's error handling, and typed, hygienic macros for what people want of Lisp's. Elm's error handling means two things here: no runtime exceptions, and compiler errors that teach. A seventh aim is a syntax that coding agents write well. Libraries, stability and ubiquity can't be designed into a language, so they get bridges outside `core`, such as editions and C source output.

The six seem to conflict: optimization with compile time, expressive types with clear errors, macros with static analysis. Stilt removes the causes of these conflicts, mainly by giving each feature one meaning and several valid ways to compile it. A debug build picks the one cheapest to compile and a release build the one fastest to run. The Reference marks each such strategy informative, so no test can observe it:

- **Generics.** The reference interpreter and the debug build pass a table of methods to each generic function, compiled once. The release build specializes each function for each type.
- **Failure.** `raise` is a typed effect, which the compiler returns as a tagged value. Nothing unwinds the stack, and a call that doesn't raise costs nothing extra ([how raising is compiled](../../reference/rationale/12-effects.md#raising-and-marking)).
- **Memory.** Heap objects are reference-counted, so a copy costs one increment, and Perceus reuse analysis turns a value that nothing else holds into an update in place.

When two aims still pull against each other, [Goals](../design/goals.md#priorities) fixes the order: one meaning, safely; then clarity; then speed, by build mode; then expressiveness. The feature that loses is simplified or moved to a later tier.

Some aims can't hold as stated. Whether a program overflows, runs out of memory or terminates is undecidable, so "no runtime exceptions" means three narrower things. Code under `without panic` has no operation that can panic but integer overflow, which `without overflow` rules out too. A stack overflow or running out of memory ends the process. Every failure that a caller can handle is a `raise` in a function's type ([Panics](../../reference/12-effects.md#panics)). Inferring higher-rank types is undecidable too, one more reason every signature is written.

## A language specified before it is compiled

The [Reference](../../reference/) states the language paragraph by paragraph, a reference interpreter implements it, and a conformance suite checks every implementation against it. The compiler came last, and is tested against all three. The order comes from the projects of 2026 in which agents built compilers. Agents converge when they can check their output against an oracle, and the agents that wrote a C compiler had GCC. Stilt had no GCC, so it built one first: `stilt-ref`, an interpreter in OCaml that shares no code with the compiler and is slow on purpose.

The suite judges an implementation on what it can observe: the code, file and line of each diagnostic, standard output, the exit status, and which tests pass ([What is observable](../../reference/01-conformance.md#what-is-observable)). Expected results come from the Reference, never from running an implementation. Comparing message text would tie conformance to wording, so messages are tested separately, with snapshots. Matching codes without lines can't tell an error on the right line from the same error elsewhere. Matching only some diagnostics lets cascades pass, so the Reference fixes which diagnostics are root causes ([Root causes](../../reference/18-errors.md#root-causes)).

The cost is precision everywhere. The Reference settles what most languages leave open: the digits a float prints, the order a map iterates in, the text `"{x}"` gives for every type, and the line each diagnostic is reported on. Warnings are part of conformance, so a new lint can fail existing tests. Even `std.cli.args()` leaves out the program name, because the interpreter and a compiled binary run from different paths.

## Syntax

[Values and types](02-values.md) and [Expressions](03-expressions.md) teach these forms, and the rationale of [the syntax](../../reference/rationale/03-syntax.md) and of [lexical structure](../../reference/rationale/02-lexical.md) gives the full argument.

**One syntax, in one format.** The six constructs for agents are part of the language's only syntax, and `stilt fmt` has no options ([The canonical format](../../reference/03-syntax.md#the-canonical-format)). A second syntax for agents would split what models learn from and give every tool two inputs. A configurable formatter, which `gofmt` also refuses, makes every option another canonical form, with noisier diffs. The cost is that some things have two spellings, such as a `match` and a let-else, or `|c| c.hp` and `.hp`.

**Newlines end statements, as in Go.** A newline ends a statement after a name, a literal, a closing bracket and a few other tokens. The line goes on when the next one starts with `.`, `else`, `catch`, `|` or `without` ([Newlines and terminators](../../reference/02-lexical.md#newlines-and-terminators)). Swift and Kotlin let the parser decide, which scatters the rule across the grammar. The cost: `>` and `>>` end a line, since they can close a generic type, so a comparison split across lines needs parentheses.

**Case is part of the grammar.** An uppercase name is a type, a type parameter, a variant, a trait or a constant; a lowercase one is anything else ([Identifiers and case](../../reference/02-lexical.md#identifiers-and-case)). So a pattern knows from its text that `hp` binds and `Fire` is a variant. Go uses case for visibility, which Stilt can't, since case already has a meaning. The cost is that naming conventions are rules: a constant can't be lowercase.

**Line comments only, and commented-out code is a warning.** A `//` comment whose text parses as code gets W0001 ([Comments](../../reference/02-lexical.md#comments)). Agents treat comments as authoritative, and broken commented-out code measurably raises the rate of broken generated code. Block comments would make such code harder to find, and Zig works without them. Prose that happens to parse, such as `// f(x)`, gets the warning too.

**Strings interpolate, and nothing else builds them.** Every string literal interpolates `{expr}`, and `\{` writes a brace, like every other escape, where Python and Rust write `{{`. `+` isn't defined on `str`, and the error for `a + b` offers `"{a}{b}"`.

**A format width has no leading zero.** In Python and Rust, `{n:05}` pads with zeros. Stilt's specs have no zero flag, so `{n:05}` is E0007, *malformed format spec*, and never means something else ([Showing and formatting](../../reference/17-std.md#showing-and-formatting)). Zeros are a fill and an alignment:

```stilt
fn main() / io {
  let hp = 7
  print("{hp:0>5} {-hp:0>5}")
}
```

```output
00007 000-7
```

The fill pads the shown text, sign included, so a negative number gets its zeros before the `-`, where Python's `{:05}` gives `-0007`.

**ASCII names, and no `char`.** Identifiers are ASCII, because characters that look alike would let two different names look like one ([Identifiers and case](../../reference/02-lexical.md#identifiers-and-case)). Text is always a `str`, and `chars()` splits one into strings of one character each, since a `char` type would give every text operation two forms.

**The words of every tier are reserved in every module, and no others.** Fifteen words, such as `comptime`, `effect` and `unsafe`, and the tokens `@`, `'` and `#`, are reserved in `core` too ([Keywords](../../reference/02-lexical.md#keywords)). So every file has one grammar, and a module that starts to use a later tier never renames a binding. Words that no tier uses, such as `mut` and `ref`, stay free: a reserved word costs everyone a name.

## Values and memory

[Values and types](02-values.md) teaches the value model, and its [rationale](../../reference/rationale/05-values.md) gives the full argument.

**Values are copied, never moved.** Assigning a value, passing it, binding it in a pattern and capturing it in a closure each make an independent copy, as the opening example shows ([Value semantics](../../reference/05-values.md#value-semantics)). Rust and Hylo use affine moves, which add a class of errors for a performance property the tools already show. In return, no other code can change a value you hold, and `core` is safe with no borrow checker. The cost is that speed rests on the compiler, and mutable state with one identity takes `Shared<T>`, from the advanced tier.

**Which parameters a function consumes is inferred.** A function **consumes** a parameter when its body returns it, stores it, or passes it on to a callee that consumes it. A caller that passes its last use of a value to such a parameter gives it up, and the callee changes it in place. A caller that keeps the value gets a copy:

```stilt
fn joined(roster: List<str>, name: str) -> List<str> {
  var bigger = roster
  bigger.push(name)
  bigger
}

fn main() / io {
  var roster = ["Embercat"]
  roster = joined(roster, "Mossling")
  let full = joined(roster, "Tidepup")
  print("{roster} {full}")
}
```

```output
["Embercat", "Mossling"] ["Embercat", "Mossling", "Tidepup"]
```

The first call hands `roster` over, so `push` grows it in place. The second keeps using `roster`, so `joined` copies the list first, and `stilt show` points out the lost reuse. In Rust, reading `roster` after the move would be an error. A written `own` mode lost because the caller can't observe it, so writing it would declare a compilation strategy ([Passing values](../../reference/rationale/05-values.md#passing-values)). The cost is that a reader without tools doesn't see which arguments a function consumes.

**`inout` keeps the changes made before a raise.** An `inout` argument holds every change the callee made, whether it returns or raises:

```stilt
type Full = | Full(name: str)

fn recruit(inout roster: List<str>, names: List<str>) / raise<Full> {
  for name in names {
    if roster.len() == 2 { raise Full(name) }
    roster.push(name)
  }
}

fn main() / io {
  var roster = []
  let names = ["Embercat", "Mossling", "Tidepup"]
  try recruit(inout roster, names) catch Full(name) => print("no room for {name}")
  print("{roster}")
}
```

```output
no room for Tidepup
["Embercat", "Mossling"]
```

Rolling `roster` back would mean copying every `inout` argument on entry to every function that can raise, a hidden cost. So a caller that catches the error sees a half-finished change. Code that needs all or nothing passes a copy and assigns it back when the call succeeds.

**`str` is owned text.** A `str` is immutable UTF-8, compared by its text, and behaves as every other value does. In `core`, `slice` returns a new `str`; a view into a string comes with the advanced tier.

**Evaluation is strictly left to right.** Arguments, operands, elements and fields are evaluated in the order they are written ([Evaluation order](../../reference/05-values.md#evaluation-order)). C leaves the order of arguments open, and Stilt fixes it so that two implementations print the same output. One consequence is subtle: an `inout` place is read when the call starts, after every argument, so in `xs.push(xs.pop() else 0)` the `pop` reaches the callee.

## Numbers

[Values and types](02-values.md) teaches the numeric types, and the [rationale of numbers](../../reference/rationale/06-numbers.md) gives the full argument.

**Fixed-width integers, and lengths are `i64`.** The integer types are `i8` to `i64` and `u8` to `u64`, and there is no `usize` ([Numeric types](../../reference/06-numbers.md#numeric-types)). Rust's unsigned lengths invite bugs when you subtract from them. Go, Java and Swift use signed lengths, and `i64` holds every real length. On 32-bit targets and WebAssembly, lengths are checked at the boundary.

**Overflow panics in every build.** Integer `+`, `-` and `*` panic with kind `overflow` when the result doesn't fit, and `+%`, `-%` and `*%` wrap ([Arithmetic](../../reference/06-numbers.md#arithmetic)). Rust wraps in release builds, which gives its two builds different meanings. The cost is a check on every operation. A check that blocks vectorization slowed a summing loop 3 to 12 times in a C measurement, which a [goal](../design/goals.md#run-time-performance-c) watches.

**No implicit conversions.** Both operands of an arithmetic operator or a comparison have one type, so `hp * rate` with `hp: i64` and `rate: f64` is E0311, whose message suggests `to_f64()` ([Conversions](../../reference/06-numbers.md#conversions)). A conversion that can lose the value, such as `i64.to_u8()`, gives an `Option`. Implicit conversions make mistakes that resist a clear message. A shift's amount can have any integer type, since `u64` bits are shifted by an `i64` count far more often than by a `u64`.

**A literal takes its type from its context.** A number literal has no suffix, takes the type the body gives it, and is an `i64` or an `f64` when nothing does ([Literals](../../reference/06-numbers.md#literals)). So a later line can decide an earlier literal's type: after `var total = 0`, a later `total += price` with `price: f64` makes the `0` an `f64`.

**Floats print exactly.** A float prints in the shortest form that reads back as the same value, in scientific notation below `0.0001` and from `1e16` up, close to Python's `repr` ([Printing](../../reference/06-numbers.md#printing)). Rust's `Display` never prints an exponent, which makes very large and very small values unreadable.

**Only correctly rounded float methods.** The float methods, such as `sqrt`, `floor` and `round`, are those IEEE 754 defines exactly. `pow`, `exp`, `sin` and `log` are functions of `std.math`, within 4 ulps of the exact result, since no two implementations can promise the same bits for them ([Numbers](../../reference/17-std.md#numbers)). Printed unrounded, they can differ in their last digits across platforms.

## Programs and modules

[Programs](08-programs.md) teaches modules, `main` and tests, and the [rationale of programs](../../reference/rationale/04-programs.md) gives the full argument.

**Modules are imported whole, and names are written qualified.** `use std.fs` binds `fs`, and code calls `fs.read(…)`; there are no item imports, aliases or re-exports ([Imports](../../reference/04-programs.md#imports)). Importing `std.fs.read` would give a name two homes and make definitions harder to grep for, and a prelude that libraries extend would be a re-export by another name. The cost is qualified names everywhere, as `fs.read` and `f64.PI`.

**Visibility is `pub`, and modules form no cycle.** Items are private unless marked `pub` ([Visibility](../../reference/04-programs.md#visibility)). Modules can't import each other in a cycle, as in Go, where each module exports a compact interface that its dependents compile against. Teams that work with agents report acyclic modules as one of the things that help. Two modules that need each other are merged, or split another way.

**`main` and the exit status are fixed.** `main` takes nothing and can perform `io` and `raise<E>` for any `E` that has `Show` ([The entry point](../../reference/04-programs.md#the-entry-point)). An error that escapes `main` prints `error: ` and the error and exits with status 1, so most programs need no handler at the top. A panic exits with 101, and a stack overflow or running out of memory with 134 ([How a program ends](../../reference/04-programs.md#how-a-program-ends)).

**Tests, examples and properties are part of the language.** `stilt test` runs `test` blocks, `/// ex:` examples and `/// prop:` properties ([Tests and doc examples](../../reference/04-programs.md#tests-and-doc-examples)), and `check` runs none of them, so it stays a fast, static answer. Hypothesis seeds a property's cases at random; Stilt takes them from the property's text, so every implementation gives the same verdict, and an agent never chases a failure that has gone.

**`run` runs a program with errors.** `run` reports the diagnostics, then runs the program, with each body that has an error replaced by a panic of kind `check-error` ([Running a program with errors](../../reference/18-errors.md#running-a-program-with-errors)). The run exits with status 2, so no script takes it for a success. Refusing to run would stop you from trying the rest of a program while you fix one function. A body is replaced whole because it is the smallest unit every implementation agrees on.

**A module's tier is inferred, never declared or limited.** No syntax names a tier, and a tier's name after `without` is E0100 ([Module headers and tiers](../../reference/04-programs.md#module-headers-and-tiers)). A declaration in the header would assert nothing that the features don't show, and could disagree with them. Haskell's language extensions, one switch per feature, make a dialect for every combination, where four ordered tiers make four. Keeping unsafe code out of a module is a matter of its facts, with `without unsafe`.

## Expressions

[Expressions](03-expressions.md) teaches these forms, and the [rationale of expressions](../../reference/rationale/08-expressions.md) gives the full argument.

**An unused value is an error.** A statement that isn't the last of its block must have type `()` or `Never` ([Statements and blocks](../../reference/08-expressions.md#statements-and-blocks)):

```stilt E0322:3
fn main() / io {
  var roster = ["Tidepup", "Embercat", "Mossling"]
  roster.sorted()
  print("{roster}")
}
```

`sorted` returns a new list and leaves `roster` alone, so line 3 would do nothing, and it gets E0322, *unused value*. `roster.sort()` sorts in place. Go and Rust discard such values, and the mistake passes in silence. Discarding a value on purpose takes `let _ = e`.

**A method's name says whether it changes its receiver.** A verb, such as `sort`, changes the receiver, which it takes `inout`, and a participle, such as `sorted`, returns a new value ([Principles](../../reference/17-std.md#principles)). Terms of art, such as `map` and `filter`, keep their names. If `sort` returned a new list, `roster.sort()` would read as sorting and do nothing.

**Assignment is a statement.** `x = e` has no value, so `if x = y` can't be written, and neither can `a = b = 0`.

**`else` has two meanings, told apart by the pattern.** `e₁ else e₂` takes the value out of an `Option`, evaluating `e₂` only for `None`. `let P = e else …` with a pattern that can fail is a let-else, whose `else` must leave ([The `else` fallback](../../reference/08-expressions.md#the-else-fallback)). In the measured orders program, these two saved 48 of the 65 tokens that the six agent constructs saved. Whether a pattern can fail follows from its text ([Refutability](../../reference/09-patterns.md#refutability)), never from the exhaustiveness check. The cost is two meanings that look alike, and a `Result` needs `.ok()` first, which drops its error.

**Fields read through an `Option`.** A field read on an `Option` gives the field of a `Some`, and `None` otherwise, with no mark to write ([Fields through an `Option`](../../reference/07-types.md#fields-through-an-option)):

```stilt
type Element = | Fire | Water | Plant

type Creature = { name: str, element: Element, hp: i64, attack: i64 }

type Trainer = { name: str, partner: Option<Creature> }

fn main() / io {
  let embercat = Creature { name: "Embercat", element: Fire, hp: 30, attack: 8 }
  let ana = Trainer { name: "Ana", partner: Some(embercat) }
  let bo = Trainer { name: "Bo", partner: None }
  print("{ana.partner.name} {bo.partner.name}")
  print(bo.partner.name else "no partner")
}
```

```output
Some("Embercat") None
no partner
```

`ana.partner.name` is an `Option<str>`, and a path holds one `Option` however many of its links are optional. Swift's and Kotlin's `?.` repeats what the type already says, and needs rules of its own for how far it reaches. Flow typing, as in TypeScript, gives one expression different types on different lines. Methods don't read through, since skipping a call on `None` could hide `io` or a raise: they go through `map` or after `else`.

**A struct literal needs an uppercase name.** `e {` starts a struct literal only after an uppercase name, so `if hp == 0 {` means what it says, and the grammar stays LR(1) ([Struct literals and heads](../../reference/08-expressions.md#struct-literals-and-heads)). A struct literal in an `if` head needs parentheses.

**No explicit type arguments.** `<` in an expression always means less-than, and annotations instantiate generic types, as `let m: Map<str, i64> = Map.new()` ([types.no-type-arguments](../../reference/07-types.md#types.no-type-arguments)). Rust's turbofish, `f::<T>()`, is clumsy, and an annotation gives inference what it needs.

**Ranges exist only in `for`.** `a..b` is the iterable of a `for` and a syntax error anywhere else ([expressions.ranges](../../reference/08-expressions.md#expressions.ranges)). A range as a value would be an iterator, which holds references that only the advanced tier's views give. `slice(start, end)` cuts a list.

**Closures copy what they capture, and can't change it.** Assigning a captured variable inside a closure is an error ([Closures](../../reference/08-expressions.md#closures)), so a capture never breaks the law of exclusivity. The cost is that a closure can't keep a counter: that state goes through `fold`, a loop, or an `inout` parameter of the closure, as `|inout c| …`.

**Key paths, positional arguments and marked `inout`.** `.hp` stands for `|c| c.hp` where a function is expected, as in `roster.map(.hp)`, to save tokens. There are no named arguments, default values or variadic functions: a `List<T>` parameter takes any number of values. `hit(embercat, inout mossling)` shows the change at the call, while a method's `inout self` receiver, as in `roster.push(name)`, has no mark.

**Bindings shadow.** `let hp = hp - 3` reads the `hp` bound before it, and `var x = x` gives a mutable copy of a parameter ([Scope](../../reference/08-expressions.md#scope)). The cost is that one name can mean different values in one body.

**Inference stays inside each body.** A body is checked in evaluation order, each expression against the type its context expects ([Inference](../../reference/07-types.md#inference)). Haskell infers across a program; checking each body against signatures alone keeps edits local and puts each error on the line of the mistake. The cost: a receiver's type must be known from the lines before it, so `|s| s.len()` with nothing to fix `s` is E0312 and needs `|s: str|`.

## Declarations and patterns

[Declaring types](04-declarations.md) teaches these forms, and the rationale of [declarations](../../reference/rationale/10-declarations.md) and [patterns](../../reference/rationale/09-patterns.md) gives the full argument.

**Records are nominal.** `type Creature = { … }` declares a new type, distinct from every other record with the same fields ([Record types](../../reference/10-declarations.md#record-types)). Anonymous records and record bounds make inference and messages harder, so they belong to the advanced tier. An update, `Creature { ..embercat, hp: 0 }`, keeps the record's type.

**No type aliases.** `type Roster = List<Creature>` is a syntax error ([No aliases](../../reference/rationale/10-declarations.md#no-aliases)). An alias gives one type two names, and messages get harder to read. The newtype idiom gives a real type: `type CreatureId = | CreatureId(i64)`, which works because types and values have separate namespaces.

**Variant payloads are positional.** In `Hit(damage: i64)`, the name documents the payload, and patterns and constructors never use it ([Variant types](../../reference/10-declarations.md#variant-types)). Named fields would give each variant two pattern forms. The cost is that nothing catches two swapped payloads of one type.

**Typed holes and constant values.** `?` stands for code not yet written: it gets W0300, the program still runs, and reaching it panics with kind `hole` ([Typed holes](../../reference/10-declarations.md#typed-holes)). An agent can then check and run a plan where it would otherwise write it in comments. A constant's initializer holds only literals, unary `-`, tuples, lists, records, variants and other constants ([Constants](../../reference/10-declarations.md#constants)), so it can panic only when a `-` overflows.

**A pattern names a variant through the type it matches.** A bare `Fire` in a pattern names the variant of the matched type, whatever module declares it ([Variants named by the matched type](../../reference/09-patterns.md#variants-named-by-the-matched-type)). The module on every arm would repeat what the type says. Expressions still qualify another module's variants, since a constructor's expected type is often unknown where it stands.

**Exhaustiveness is checked, with a missing case.** A `match` that misses a value is E0329, and the message names one, as `(Fire, Fire)` in [the tour](01-tour.md#match-the-elements), the way Elm's messages do ([Exhaustiveness](../../reference/09-patterns.md#exhaustiveness)). Guards and constants count for nothing, since proving that guards cover every case needs reasoning about values. So a `match` whose guards cover every case still needs a last arm without one.

**Patterns keep to what exhaustive matching needs.** The forms are those of ML and Rust, without range patterns, `@` bindings or elements after `..` in a list, as `[.., last]` ([Forms](../../reference/09-patterns.md#forms)). Each would add its own case to the exhaustiveness check. No literal matches a float, so a test on a float is a guard or an `if`.

**`if let` tests one pattern.** `if let Some(m) = best { … }` replaces `match best { Some(m) => …, _ => {} }`, whose do-nothing arm stood twelve times in five programs. There is no `while let`: a loop writes `let P = e else break`.

## Effects and failure

[Errors and effects](05-errors.md) teaches these features, and the [rationale of effects](../../reference/rationale/12-effects.md) gives the full argument.

**Effects are written in signatures.** A function's row, after `/`, lists `io`, at most one `raise<E>`, and at most one row variable ([Rows](../../reference/12-effects.md#rows)). Whether a function can fail or touch the world is in its type, where callers see it. The cost is that a function type inside another type matches exactly, so a `List<fn()>` isn't a `List<fn() / io>`.

**Function arguments pass their effects through.** A parameter of function type lists only what its function handles. The argument's other effects pass through to the caller, which marks them with `try` ([Parameters that pass effects through](../../reference/12-effects.md#parameters-that-pass-effects-through)). So one `map` serves pure, printing and failing callbacks, with no row variable written, where Koka writes one in every such signature. A function that keeps such a parameter marks it `escaping`, since inferring that from the body would tie callers to a body.

**One error type per row.** Code that can fail in two ways maps one error into the other where they meet:

```stilt exit:1
use std.fs

type ConfigError = | Unreadable(path: str) | BadPort(text: str)

fn load_port(path: str) -> u16 / {io, raise<ConfigError>} {
  let text = try fs.read(path) catch _ => raise Unreadable(path)
  text.trim().to_u16() else raise BadPort(text)
}

fn main() / {io, raise<ConfigError>} {
  let port = try load_port("port.txt")
  print("port {port}")
}
```

```stderr
error: Unreadable("port.txt")
```

`fs.read` raises a `std.io.IoError`, and the `catch` on line 6 turns it into a `ConfigError`. With no `port.txt`, the error escapes `main`, which prints it and exits with status 1. Several error types in one row, kept apart by scoped labels as in Koka, would leave the type of a catch-all `e` unclear. The cost is a mapping at every boundary; raising a second type without one is E0503.

**Every raising call is marked with `try`.** A call that can raise sits inside a `try`, which also covers the closures written in it, as `try lines.map(|l| parse(l))` ([Raising and marking](../../reference/12-effects.md#raising-and-marking)). You see every place a function can stop early, which Java's and Python's exceptions hide. A missing `try` is E0505, which offers the fix.

**`try` acts on `raise`, never on `Result`.** A `Result` stores failure as data, and `r.get()` and `Result.of(|| e)` move between the forms ([Failure as data](../../reference/12-effects.md#failure-as-data)). If `try` unwrapped a `Result`, as Rust's `?` does, `try f()` would be ambiguous when `f` both raises and returns one.

**A catch-all raises, uses its error or gives a reason.** `catch _ => 8080` gets W0501, and `catch _ because "old configs omit the port" => 8080` says why dropping the error is right ([Handling errors](../../reference/12-effects.md#handling-errors)). Agents tend to catch everything, and error masking rose by 47% in code changes of the AI era.

**A `catch` can't handle a failure that belongs to the caller.** A callback `f: fn()` can raise any error type, which arms written for one type can't handle. So a `catch` around the call is E0506 ([Failures that pass through](../../reference/12-effects.md#failures-that-pass-through)). Naming the type, as `f: fn() / raise<E>`, makes it fine, and passing `f` on to code that handles it needs the same, or it is E0507. The Lean model and a review found two weaker rules unsound, and a check at run time would cost every raise.

**Panics are for bugs.** An index out of range, a division by zero or an overflow panics: the program stops with status 101, and nothing catches it ([Panics](../../reference/12-effects.md#panics)). A failure a caller can handle is always a `raise`.

## Inferred facts and limits

[Errors and effects](05-errors.md) teaches `without`, and the [rationale of facts](../../reference/rationale/15-facts.md) gives the full argument.

**`panic` and `alloc` are inferred, never written.** The compiler infers whether a function can panic, overflow or allocate, and `stilt show` prints these **facts** after its signature, as the tour shows for `hit` ([Inferred facts](../../reference/15-facts.md#inferred-facts)). A required `/ alloc` would sit on almost every signature and tell you nothing. Facts stay out of types, so a change to them never checks a caller's types again. Effect variables hidden in function types would make `without alloc` exact for callbacks, but they would leak into type checking. A call through a function value adds no facts: they count where the closure is written.

**`without` turns a fact into a promise.** A module's header or a function can carry `without panic`, `overflow`, `alloc`, `div`, `copy` or a capability, and the compiler holds the code to it ([Limits](../../reference/15-facts.md#limits)):

```stilt E0204:6
module main
without panic

fn wins(winners: List<str>) -> Map<str, i64> {
  var counts = Map.with_default(0)
  for name in winners { counts[name] += 1 }
  counts
}
```

Reading `m[k]` panics on a map without a default, and whether a map has one is known only at run time, so every map read counts. Line 6 gets E0204, *fact beyond a `without` limit*, and code under the limit writes `counts.insert(name, (counts.get(name) else 0) + 1)`. One clause serves every limit, where options such as `total` and `noalloc` would be two spellings of one check. Overflow is a fact of its own, since counting it as `panic` would force a checked form on every operation under the limit.

**Every limit reads a fact the compiler already infers.** Under `without alloc`, a function writes in place to a list whose storage it holds. A caller that keeps using the list pays for its copy at the call ([Updates in place](../../reference/15-facts.md#updates-in-place)). Koka's `fip` makes callers hand over unique values; Stilt's value semantics promise a copy, never an error. `div` marks a function that might not end: a `while` that isn't a counting loop, a call through a stored function, or a recursion that doesn't shrink ([Termination](../../reference/15-facts.md#termination)). So `without panic, div` means total, judged by two shapes a reader can see.

**Capabilities are inferred below `io`.** `fs`, `net`, `clock`, `env`, `console`, `rand`, `spawn` and `exec` are inferred from the native functions a function reaches, limited with `without`, and granted to dependencies one by one ([Capabilities](../../reference/15-facts.md#capabilities)). A dependency that only prints is granted `console`. Capabilities in rows would lengthen every `/ io` signature. The cost is that a callback that reads files passes through `without fs` code, as allocations pass through `without alloc`.

## Traits

[Traits and generics](06-traits.md) teaches these features, and the [rationale of traits](../../reference/rationale/11-traits.md) gives the full argument.

**Type classes over one type, with coherence.** A trait declares methods over `Self`, a type has at most one impl of a trait, and the impl lives in the trait's module or the type's ([Traits](../../reference/11-traits.md#traits)). Traits that relate two types or abstract over containers complicate inference and coherence, so they belong to the advanced tier. In `core`, `List` and `Option` each have their own `map`.

**Methods have one home.** Inherent methods live in their type's own module, and `x.m()` never looks at the other arguments' types ([Method resolution](../../reference/11-traits.md#method-resolution)). There is no overloading, so checking never searches across candidates. To add a method to `str`, another module declares a trait. When two visible traits match, the call is E0319 and is written `Trait.m(x)`.

**Equality, ordering, hashing and printing are automatic.** Tuples, records, variant types, `List`, `Option` and `Result` get `Eq`, `Ord`, `Hash` and `Show` whenever their parts have them ([Structural impls](../../reference/11-traits.md#structural-impls)). Rust and Haskell ask for `derive`, which `core` doesn't have. The cost is that order follows declaration order, so moving a field or a variant changes how values sort.

**`Show` has a nested form.** `show` gives a `str` unchanged and `show_nested` quotes it, and containers call `show_nested` on their elements. So `"{name}"` prints `Embercat`, and `"{roster}"` prints `["Embercat", "Mossling"]`.

**Floats have two orders.** `==` and `<` on floats follow IEEE 754, and `compare`, which sorting and compound values use, is a total order:

```stilt
fn main() / io {
  let z: f64 = -0.0
  print("{z < 0.0} {(z,) < (0.0,)} {(z,) == (0.0,)}")
  let nans = [f64.NAN]
  print("{nans == nans} {nans <= nans}")
  print("{[2.0, f64.NAN, -1.0].sorted()}")
}
```

```output
false true true
false true
[-1.0, 2.0, nan]
```

Under IEEE, `-0.0` equals `0.0`, so `z < 0.0` is false. Inside a tuple, `<` goes through `compare`, where `-0.0` comes first, and `==` through `eq`, which agrees with IEEE. Every NaN sorts last. With IEEE order inside lists, sorting by a compound key would break. Floats don't implement `Hash`, so they can't be map keys ([Floats](../../reference/11-traits.md#floats)).

## Parameter modes

[Parameter modes](07-modes.md) teaches these rules, and the [rationale of modes](../../reference/rationale/13-modes.md) gives the full argument.

**Two modes, and neither can be stored.** A parameter is `let`, which reads, or `inout`, which changes the caller's place. No mode can be stored or returned, so `core` needs no lifetimes ([Places and accesses](../../reference/13-modes.md#places-and-accesses)). `inout` is the one mode a caller can observe, which is why `own` lost ([Values and memory](#values-and-memory)). The cost is that nothing in `core` holds a reference, such as an iterator over a list.

**The law of exclusivity, with lexical durations.** While a change to a place is in progress, no other access to an overlapping place can begin ([The law of exclusivity](../../reference/13-modes.md#the-law-of-exclusivity)). An `inout` argument is a change for the whole call, and a `let` argument is a read that ends before it. Rust's non-lexical lifetimes accept more programs, but `core` references can't escape, so the extra precision isn't worth a harder rule. Indexes are ignored, so `swap(inout xs[0], inout xs[1])` is E0402, while two distinct fields are fine.

**Changing a list while a loop reads it is an error.** Inside a `for` loop over a place, a change to an overlapping place is E0404, *changing a list while reading it*:

```stilt E0404:8
type Element = | Fire | Water | Plant

type Creature = { name: str, element: Element, hp: i64, attack: i64 }

fn remove(inout roster: List<Creature>, name: str) { roster.retain(|c| c.name != name) }

fn prune(inout roster: List<Creature>) {
  for c in roster { if c.hp == 0 { remove(inout roster, c.name) } }
}
```

Copy-on-write would keep this safe, by copying the whole list while the loop reads the old one. That hidden copy, and a loop that reads creatures you removed, make it an error. The fix is `roster.retain(|c| c.hp > 0)`, or collecting names in the loop and removing them after it.

**Every other mode is a fact.** Locality, uniqueness, once, portability and contention are inferred for every local, closure and parameter, and `stilt show` prints a mode that isn't the default ([Modes](../../reference/13-modes.md#modes)). OxCaml writes modes, as `local_` and `once_`, which declares a strategy no observation can tell apart. Rust's `Send` and `Sync` say what a type's declaration already says. The rules are lexical and conservative: a parameter used on two branches is `many`, though one runs.

## The advanced tier

The `advanced` tier's chapters start at [Views and iterators](11-views.md).

**A view is a window that can't escape.** `View<T>` reads part of a `str` or a `List` without copying it, and can be a local, a parameter, a result or a capture, and nothing else ([Views](../../reference/13-modes.md#views)). A result views every argument it could view, so no signature carries a lifetime, and the law of exclusivity keeps the source still while the view lives. The cost is that a view of a local can't be returned.

**Iterators are lazy, and their adapters' closures have no effects.** `Iter<T>` reads its source one element at a time ([Iterators](../../reference/13-modes.md#iterators)). An adapter's closure runs in whatever function consumes the iterator, so it can't perform `io` or raise. A row in the type, `Iter<T, row>`, would follow iterators through every signature.

**A projection yields a place.** A function whose result is written `inout T` hands its caller a place to write, as a map entry kept in step with a cache ([Projections](../../reference/13-modes.md#projections)). Its mode is written, since it changes what type-checks at every caller. Hylo's bundles of `let`, `inout` and `set` accessors make three forms of one rule. A `var` binding of a view made from an `inout` place writes through it ([Writable views](../../reference/13-modes.md#writable-views)), which lets `par` write the parts of a list in parallel.

**A trait's parameters are fixed by its impl's type.** `impl<T> Collection<T> for List<T>` gives `Collection` its parameter, which code names `C.Item` ([Trait parameters](../../reference/11-traits.md#trait-parameters)). Rust's `From<T>` takes a parameter independent of `Self`, which resolves calls by argument types, a form of overloading. So a type converts to one other type through a trait.

**Trait functions without `self`, and constructor traits.** `T.empty()` names its type; Haskell resolves `mempty` from the type a call is expected to have, so a call's meaning depends on its context. A trait that writes `Self<A>` is over a type constructor, as `impl Mappable for List` ([Constructor traits](../../reference/11-traits.md#constructor-traits)). `Result` and `Map`, with two arguments, implement none of one.

**An argument can stay generic.** `fn<T: Show>(T) -> str` is a function type with its own type parameters, instantiated at each call ([Polymorphic function types](../../reference/07-types.md#polymorphic-function-types)). GHC allows such types anywhere, but inferring a type argument that is itself generic is undecidable. So there is no list of generic functions. Polymorphic recursion, a generic function that calls itself at another type, is `core`, since its signature is written.

**`Lazy<T>` is pure.** `Lazy.new(f)` keeps a function with an empty row, computed by the first `get` ([Lazy values](../../reference/07-types.md#lazy-values)), so no program can tell when it ran. With effects in `f`, when they happen would depend on which code asks first. Haskell's laziness by default makes performance hard to predict.

**Fields are bounds, and packs are mapped.** Every record with a `name` field meets the bound `P: { name: str, .. }`, and the function gives back the caller's type ([Record bounds](../../reference/07-types.md#record-bounds)). A row variable, as in `{ name: str | r }`, would add inference for the same result. `..Ts` stands for any number of types, and a body maps over them with `(..e)` ([Variadic generics](../../reference/07-types.md#variadic-generics)). C++ templates take packs apart by head and tail, which turns each variadic function into a type-level program.

**Pattern macros are marked and hygienic.** A use of a `syntax` macro is written `name!(…)`, so a tool parses a file without resolving names ([Pattern macros](../../reference/16-meta.md#pattern-macros)). Each template is checked where it is declared, and the names it binds are its own, so a macro can't make a name its caller sees.

**The caller chooses an effect's implementation.** `effect` declares operations, and `with` installs a handler for a block, which gives test doubles and logging with no parameter threaded through ([Handlers](../../reference/12-effects.md#handlers)). A handler resumes at most once, since two resumptions would share values the value model gives one owner. Effekt passes effects as parameters, but rows already say what a function performs.

**`async` is an effect, and its meaning is the sequential run.** `task.spawn` and `t.await()` perform `async`, and what tasks print appears in the sequential order under threads too ([The sequential run](../../reference/14-tasks.md#the-sequential-run)). Rust's and JavaScript's `async fn` colour functions and split libraries in two. The cost is that a task's output waits until the tasks before it end.

**Shared state is reached in `when`, all at once.** A `Shared<T>` is reached only in `when`, which holds every value it names before it runs, and no `when` runs inside another ([Holding shared values](../../reference/14-tasks.md#holding-shared-values)). Locks taken in opposite orders deadlock, and Verona's asynchronous `when` runs code out of the order it reads in. Inferred modes say which values can cross threads, with no `Send` or `Sync`.

**Cycles through shared values are freed.** A cycle of handles that nothing else reaches is freed by trial deletion of the shared objects alone ([Cycles](../../reference/14-tasks.md#cycles)). Rust and Swift leak such cycles, and a weak handle asks about freeing, which Stilt keeps unasked. A tracing collector for the whole heap would pause programs that make no cycle.

**Parallel loops perform nothing.** `std.par` is part of `core`, and its closures have an empty row, so `par.map(xs, f)` is `xs.map(f)` on every core ([Parallel calls](../../reference/14-tasks.md#parallel-calls)). If they could raise, which raise wins would depend on the scheduler. `fold` combines in a tree fixed by the list's length, so a float fold can differ from a loop.

## The meta tier

[Value parameters, staging, reflection and procedural macros](18-compile-time.md) teaches the `meta` tier, and the rationale of [compile-time code](../../reference/rationale/16-meta.md) gives the full argument.

**A type can take a value, and a generic body is checked once.** A value parameter has an integer type or `bool`, and its arguments are literals, constants and value parameters, as in `Array<T, n>` ([Value parameters](../../reference/07-types.md#value-parameters)). A debug build passes it as a hidden argument, and a release build specializes. Arithmetic, as `Array<T, n + 1>`, would mean solving equations between types, which kept Rust's `generic_const_exprs` unstable for years.

**A staging annotation never adds a second body.** `comptime` marks a loop, a condition or a `match` whose controlling parts are static, and the program without the annotation is its meaning ([Staging annotations](../../reference/16-meta.md#staging-annotations)). A second body for compile time would mean different things in different builds. Zig reports a panic in static code as a compile error, so a program could fail in release builds alone.

**Reflection is a value, and no arm refines a type.** `T.shape()` is an ordinary value of `std.meta`, whose cases give accessors ([Shapes](../../reference/16-meta.md#shapes)). A field's type in an arm is a fresh type that code passes on but can't name, since Stilt never narrows a type in a branch. Whether a function reflects is inferred, so no `T: Reflect` bound spreads through generic code. Debug builds read shapes at run time, at 1.5 to 1.7 times the cost of hand-written code.

**`std.json` is a derive written in Stilt.** It reads and writes any type through its shape, and a type that needs another format implements `ToJson` and `FromJson` ([JSON](../../reference/17-std.md#json)). serde's `derive` generates impls, which gives a type an API from compile-time code and costs compile time for each type.

**A procedural macro reads tokens, writes quotes and performs nothing.** A macro is a function from syntax to syntax, imported with `meta use`, that runs in the compiler within 10 million steps ([Procedural macros](../../reference/16-meta.md#procedural-macros)). Rust's proc-macro crates run with your permissions during a build. A macro that took code apart as a tree would break with every change to the grammar.

## Calling C

[Programs](08-programs.md#calling-c) teaches these rules, and the [rationale of builds](../../reference/rationale/20-builds.md#foreign-functions) gives the full argument.

**C is reached through a safe wrapper, with the reason beside the call.** A foreign function takes numbers, `bool`, a `c.Ptr` and a `c.Str`, and each call stands in an `unsafe because "reason"` block ([Unsafe code](../../reference/20-builds.md#unsafe-code)). Rust's `unsafe` block gives no reason, where this one says why the call is sound. The function that holds the block has the facts `unsafe` and `foreign`, and no caller inherits them, or `without unsafe` would forbid every library that wraps C. `without` can't see into C, so a wrapper under `without alloc` can call C that allocates.

**Libraries load when the program starts.** An executable loads the libraries it names before its code runs, as `run` does, so a C function is found the same way under every command ([Calls into C](../../reference/20-builds.md#calls-into-c)). Linking each library in, as `-lz` does, would need the system's SDK on macOS. A missing symbol is found at its first call.

## The standard library

[The standard library](09-library.md) describes the library, and its [rationale](../../reference/rationale/17-std.md) gives the full argument.

**A small native core, and the rest in Stilt.** Every native function is a place where the interpreter and the compiler can disagree, so natives are few, each with conformance tests of its own ([Principles](../../reference/17-std.md#principles)). The rest is written in Stilt, in [`std/`](../../std/), and both implementations run it. Integer and string methods are native, since in Stilt each integer method would be written once per width.

**An everyday library.** The library has what everyday programs reach for, from padding text and grouping lists to sets, heaps, files and clocks. Each function takes its name and meaning from Rust, Python, Kotlin or Go, whichever most agree on. With a minimal library, every program would write the same helpers under different names, and an agent would read them before trusting them.

**Library functions don't panic, except for stated preconditions.** They return an `Option` or raise, apart from indexing and a few bounds such as those of `slice` ([Principles](../../reference/17-std.md#principles)). So code under `without panic` uses `roster.get(i)`.

**Results are the same in every implementation.** `Rng` is SplitMix64 written in Stilt, so a seed gives the same numbers everywhere ([Random numbers](../../reference/17-std.md#random-numbers)). Maps iterate and print in insertion order, so two equal maps can print differently ([Maps](../../reference/17-std.md#maps)).

**Strings count bytes.** Lengths and offsets count bytes, so slicing is constant time, while a format width counts what a reader sees ([Strings](../../reference/17-std.md#strings)). The methods of `str` change case and trim in ASCII only. Unicode's tables live in `std.text`, written in Stilt, since tables in each implementation's own language are a classic source of disagreement ([std.text](../../reference/17-std.md#std.text)). So `"é".len()` is 2.

**Names stay out of the way of variables.** A local can't share an imported module's name, so the clock module is `clock`, and path functions live in `std.fs`, leaving `path` free for variables. `Set` is in the prelude beside `List` and `Map`, and the rarer `Deque` and `Heap` are in `std.collections`.

**Output is read as it is written.** Each line `print` writes reaches standard output when `print` returns, and `io.poll_line()` gives a waiting line of input or `None`, without blocking ([Input and output](../../reference/17-std.md#input-and-output)). A chess engine can then print each depth of its search and stop when `stop` arrives, with no threads. The cost is a write for every line, as with Rust's `println!`.
