# Programs

A program can live in several files. Here the arena keeps its creatures in a module of their own, `roster`, which `main` imports:

```stilt fragment
// roster.lt
pub type Element = | Fire | Water | Plant

pub type Creature = { name: str, element: Element, hp: i64, attack: i64 }

/// The three creatures of the arena.
pub fn all() -> List<Creature> {
  [
    Creature { name: "Embercat", element: Fire, hp: 30, attack: 8 },
    Creature { name: "Mossling", element: Plant, hp: 34, attack: 6 },
    Creature { name: "Tidepup", element: Water, hp: 32, attack: 7 },
  ]
}

// main.lt
use roster

fn main() / io { for c in roster.all() { print("{c.name}: {c.hp} HP") } }
```

```console
$ stilt run
Embercat: 30 HP
Mossling: 34 HP
Tidepup: 32 HP
```

Each file is a **module**, named after its path: `roster.lt` is the module `roster`. `use roster` imports it, and `main` names its items through it, as `roster.all()`. Only the items marked `pub` can be used from another module.

## Files and modules

A program takes one of three forms ([program.forms](../../reference/04-programs.md#program.forms)):

| Form | Root directory | Module root |
| --- | --- | --- |
| A single file | The directory that holds the file | The file itself, which is module `main` whatever its name |
| A directory program: a directory that holds `main.lt` | The directory | The directory |
| A package: a directory that holds `stilt.toml` | The directory | Its `src/` folder |

Below the module root, every `.lt` file is a module, named after its path:

| File | Module |
| --- | --- |
| `main.lt` | `main` |
| `roster.lt` | `roster` |
| `battle/rules.lt` | `battle.rules` |

Each part of the path, without the `.lt`, must be a lowercase identifier that isn't a reserved word or a primitive type name. The first part can't be `std`, which names the standard library. So `Roster.lt` and `my-roster.lt` are E0200, *invalid module name* ([program.module-names](../../reference/04-programs.md#program.module-names)). Files and directories whose names start with `.` aren't part of the program. Every path that a tool reports, such as where a panic happened, is relative to the root directory and uses `/`.

A single file is module `main`, whatever the file is called. A module header that names it anything else is E0201, *module header doesn't match its file*:

```stilt E0201:1
module roster

fn main() / io { print("the arena opens") }
```

A module holds items: functions, types, traits, constants, `impl` blocks and tests.

## Importing modules with `use`

`use a.b.c` makes the module `a.b.c` available under the name `c`, and code names its items through that name ([program.what-use-binds](../../reference/04-programs.md#program.what-use-binds)). Run with no arguments, this program prints its default name:

```stilt
use std.cli

fn main() / io {
  let name = cli.arg(0) else "Embercat"
  print("{name} enters the arena")
}
```

```output
Embercat enters the arena
```

`use` imports modules, never single items, and there are no import aliases and no re-exports. A module uses its own items and the prelude's without a qualifier. Every other name is written with one: an item of another module through its module, as `fs.read`, and a member of a type through the type, as `f64.PI`. So every name has exactly one home, and its qualifier tells you where it is defined.

A `use` that names an item, as Rust's `use std::fs::read` would, is E0230, *`use` of an item*. Its fix imports the module, `use std.fs`, so that code writes `fs.read`:

```stilt E0230:1
use std.fs.read

fn main() / io {
  let text = try read("arena.txt")
  print(text)
}
```

The names that `use` binds share one namespace with functions, constants, variants and local bindings. A local binding can shadow an item, but not an imported module: that is E0207, *local named after an imported module*:

```stilt E0207:4
use std.fs

fn main() / io {
  let fs = "arena.txt"
  print(fs)
}
```

These rules come up less often ([Imports](../../reference/04-programs.md#imports)):

- A `use` that names no module is E0205, *unknown module*. A `use` can also name a prefix of a module's name: after `use std`, `std.io.read_line()` works.
- Two `use` declarations that bind the same name are E0208, *name defined twice*. Import the parent of one of the two modules instead, and reach that module through it.
- Modules can't import each other in a cycle: that is E0206, *import cycle*.
- A pattern names a variant without its module, through the type it matches. A `match` on a `roster.Element` writes `Fire` on its arms, while code that builds one writes `roster.Fire`.

## Visibility

An item is private to its module unless it is marked `pub`. Naming another module's private item is E0213, *private item*. Fields and variants have their type's visibility, and the functions and constants of an inherent `impl` block need their own `pub`. The methods of a trait impl are visible wherever both the trait and the type are, and are written without `pub` ([program.visibility](../../reference/04-programs.md#program.visibility)).

A signature that other modules see can't name a private type, because they couldn't name it either. That is E0214, *private item in a public signature*, at the private type:

```stilt E0214:3
type Score = { wins: i64, losses: i64 }

pub fn score() -> Score { Score { wins: 3, losses: 1 } }
```

To fix it, mark `Score` as `pub` too. Visibility is written with `pub`, and not by capitalization as in Go, because case already means something: an uppercase name is a type, a variant, a trait or a constant.

## The prelude

The **prelude** is the set of names that every module sees without a `use`. It holds the primitive types, `Never`, `Option`, `Result`, `List`, `Map`, `Set` and `Ordering`, their variants, the traits `Eq`, `Ord`, `Hash` and `Show`, and five functions ([program.contents](../../reference/04-programs.md#program.contents)):

| Function | Behaviour |
| --- | --- |
| `print(s: str) / io` | Writes `s` and a newline to stdout |
| `eprint(s: str) / io` | Writes `s` and a newline to stderr |
| `exit(code: u8) -> Never / io` | Flushes both output streams and ends the process with `code` |
| `panic(msg: str) -> Never` | Panics with the kind `explicit` |
| `unreachable() -> Never` | Panics with the kind `unreachable` |

No library adds to the prelude. A module can't declare an item or import a module with the name of a prelude item in the same namespace, such as a type named `Option`. That is E0209, *name of a prelude item*:

```stilt E0209:1
type Option = | Fight | Flee
```

Types and traits share one namespace, and functions, constants, variants and modules share the other, so a variant named `Eq` or `List` is fine ([program.prelude-namespaces](../../reference/04-programs.md#program.prelude-namespaces)). A local binding can still shadow a prelude function, as it can any item.

## Module headers, tiers and limits

A file can begin with a **header**: `module`, the module's name, and optionally a `without` clause that limits what the compiler infers about the module's code ([program.module-header](../../reference/04-programs.md#program.module-header)). The name must be the module's own:

```stilt
module main
without panic, overflow

fn main() / io { print("checked as code that can't panic") }
```

```output
checked as code that can't panic
```

Each limit rules out one kind of operation in the module's functions, and an operation beyond a limit is E0204. [Limits](05-errors.md#limits) shows each one at work:

| Limit | What it rules out |
| --- | --- |
| `panic` | Every operation that can panic, other than by overflow |
| `overflow` | Every operation that can overflow ([Overflow](05-errors.md#overflow)) |
| `alloc` | Every operation that allocates |
| `div` | Every operation that might not end ([Termination](05-errors.md#termination)) |
| `copy` | Every write that copies shared data ([Copies](05-errors.md#copies)) |
| `locks` | Every `when`, and every call of a function that runs one ([Shared state](17-effects.md#shared-state)) |
| `fs`, `net`, `clock`, `env`, `console`, `rand`, `spawn`, `exec` | Every use of the capability ([Capabilities](05-errors.md#capabilities)) |
| `unsafe` | Every `unsafe` block of the module's own code ([Calling C](#calling-c)) |

A header holds one `without`, which names each limit once. A second `without`, or a limit named twice, is E0202, *`without` given twice*, at the second one. A function can carry a `without` of its own ([Declaring types](04-declarations.md#functions)).

```stilt E0202:2
module main
without panic, overflow, panic

fn main() / io { print("panic is already named") }
```

The language comes in four **tiers**, ordered `core`, `advanced`, `meta` and `systems`, and each one allows everything the tiers before it allow. `advanced` adds features such as views, effects of your own and pattern macros. `meta` adds value parameters and code that runs while the program compiles, and `systems` adds calls into C ([program.tiers](../../reference/04-programs.md#program.tiers)). Each chapter of a later tier says which features put a module in it.

A module's tier is never written. It is the first tier that allows every feature the module uses: the compiler infers it, and `stilt show` prints it with each function, as `module main [core]`. A module that uses only core features is a core module, with or without a header. A tier's name after `without` is a syntax error, E0100.

## The entry point

A program starts at the function `main` of the module `main`. It takes no parameters, returns `()`, and its row holds at most `io`, a `raise<E>` whose `E` implements `Show`, and `async` ([Effects, tasks and parallelism](17-effects.md)). Any other signature is E0310, *invalid `main`* ([program.main](../../reference/04-programs.md#program.main)):

```stilt E0310:1
fn main(args: List<str>) / io { print("{args}") }
```

The command-line arguments come from `std.cli`, as `cli.args()` and `cli.arg(0)`, and standard input from `std.io`, as `io.read_line()` ([Read input and write output](09-library.md#read-input-and-write-output)). `check` and `test` don't need a `main`, so a library has none.

## Exit statuses

How a program ends decides its exit status ([program.exit-statuses](../../reference/04-programs.md#program.exit-statuses)):

| How the program ends | Exit status |
| --- | --- |
| `main` returns | `0` |
| It calls `exit(code)` | `code` |
| A raise escapes `main` | `1`, after printing `error: {e}` to stderr ([Errors that escape `main`](05-errors.md#errors-that-escape-main)) |
| A panic | `101`, after the panic report ([Panics](05-errors.md#panics)) |
| A stack overflow, or running out of memory | `134`, after printing `fatal: ` and a reason to stderr ([Memory and recursion](#memory-and-recursion)) |
| Its standard output is closed, as by `head` once it has read enough | `141`, printing nothing more |
| The program has errors | `2`, however it ends ([Programs with errors](#programs-with-errors)) |
| `run` finds no `main` | `2`, without running anything |

`exit` has the type `Never`, so it fits wherever a value is expected, such as in a `catch` arm. It flushes both output streams, then ends the process:

```stilt exit:3
fn main() / io {
  print("2 of 3 battles fought")
  eprint("Tidepup didn't arrive")
  exit(3)
}
```

```output
2 of 3 battles fought
```

```stderr
Tidepup didn't arrive
```

Output doesn't wait for the end: each line that `print` writes reaches stdout when `print` returns, so a program that prints its progress is read as it goes ([program.output-flushing](../../reference/04-programs.md#program.output-flushing)).

## Memory and recursion

A stack overflow and running out of memory aren't panics: each one aborts the program with status 134. Every implementation supports a call depth of at least 10,000 calls of ordinary functions ([program.recursion-depth](../../reference/04-programs.md#program.recursion-depth)). How much memory a program can use is up to each implementation. The reference interpreter allows 512 MiB of heap. A program that the compiler runs or builds gets a stack of 1 GiB, enough for a recursion millions of calls deep. Its heap is as large as the machine's memory, or the size that `STILT_HEAP` names, as `STILT_HEAP=512M`.

## Tests

A **test** is an item, `test "name" { body }`, and `assert expr` panics with the kind `assert` when `expr` is false. A test passes when its body ends without raising, panicking or calling `exit`. A failure ends only its own test, and the tests after it still run ([Tests and doc examples](../../reference/04-programs.md#tests-and-doc-examples)):

```stilt pass:12 fail:14 fail:20 pass:22
type Element = | Fire | Water | Plant

type Creature = { name: str, element: Element, hp: i64, attack: i64 }

fn remaining(hp: i64, damage: i64) -> i64 { (hp - damage).max(0) }

fn hit(attacker: Creature, inout defender: Creature) / raise<str> {
  if attacker.hp == 0 { raise "{attacker.name} has fainted and can't move" }
  defender.hp = remaining(defender.hp, attacker.attack)
}

test "hit points never go below zero" { assert remaining(3, 8) == 0 }

test "a raise fails the test" {
  let fainted = Creature { name: "Embercat", element: Fire, hp: 0, attack: 8 }
  var mossling = Creature { name: "Mossling", element: Plant, hp: 34, attack: 6 }
  try hit(fainted, inout mossling)
}

test "a false assert fails the test" { assert remaining(30, 8) == 21 }

test "later tests still run" {
  let embercat = Creature { name: "Embercat", element: Fire, hp: 30, attack: 8 }
  var mossling = Creature { name: "Mossling", element: Plant, hp: 34, attack: 6 }
  try hit(embercat, inout mossling)
  assert mossling.hp == 26
}
```

A test body can perform `io` and raise any error that implements `Show`, so it calls `hit` with `try` and no `catch`. `stilt test` runs every test, doc example and property of the program's own modules, and reports each failure with its line and its reason. For this program, the compiler prints:

```text
main.lt:14: test "a raise fails the test" failed
  raised Embercat has fainted and can't move
main.lt:20: test "a false assert fails the test" failed
  panic: assert: the assertion is false: 22 == 21
    at main.lt:20:40
2 passed, 2 failed
```

`check` and `run` run no tests, so `check` stays fast. Two tests of one module with the same name are E0208, *name defined twice*. `stilt test --json` writes the results as one JSON object, which editors read to show each result where it is written ([The command line](../commands.md#stilt-test)).

## Documentation examples

A run of `///` lines documents the declaration right below it, and its first line is the summary. A doc line that starts with `ex:` is an **example**: a `bool` expression that `stilt test` runs with the tests. It passes when it is `true`, and fails when it is `false`, raises or panics ([program.doc-examples](../../reference/04-programs.md#program.doc-examples)):

```stilt pass:2 pass:3 fail:4
/// The hit points left after taking `damage`, never fewer than zero.
/// ex: remaining(10, 4) == 6
/// ex: remaining(3, 5) == 0
/// ex: remaining(10, -4) == 10
fn remaining(hp: i64, damage: i64) -> i64 { (hp - damage).max(0) }
```

The third example fails, because a negative `damage` heals: `remaining(10, -4)` is `14`. An example is checked as a test body of its module is, so it can use `try`, and a module's `without` limits don't apply to it. Because `stilt test` runs the examples, the documentation can't drift from the code.

## Properties

A doc line that starts with `prop:` is a **property**: a closure that must return `true` for every value of its parameters. `stilt test` generates values for the parameters and looks for ones that make it `false` ([Properties](../../reference/19-tools.md#properties)):

```stilt pass:2 fail:3
/// The hit points left after taking `damage`, never fewer than zero.
/// prop: |hp: i64, damage: i64| hp < 0 || damage < 0 || remaining(hp, damage) <= hp
/// prop: |hp: i64, damage: i64| remaining(hp, damage) < hp
fn remaining(hp: i64, damage: i64) -> i64 { (hp - damage).max(0) }
```

The second property is wrong: a hit with no damage leaves the hit points as they were. The first one states its precondition with `||`, so a case with a negative value passes without calling `remaining`.

Each parameter has its type written, and the types are all that decide how values are generated: you write no generator. The first case gives each parameter its smallest value, such as `0`, `""` or `[]`. Later cases try larger values, and values at the edges of the type, such as `i64.MAX` ([Cases](../../reference/19-tools.md#cases)). The values come from a seed computed from the property's text, so a property tries the same cases on every run. When a case fails, `stilt test` shrinks its values to a small counterexample before it reports them ([Running and shrinking](../../reference/19-tools.md#running-and-shrinking)).

A property that isn't a closure with typed parameters is E0332, *property that isn't a closure with typed parameters*. A parameter type that can't be generated, such as a function type or `Never`, is E0333, *parameter type that can't be generated* ([Types that can be generated](../../reference/19-tools.md#types-that-can-be-generated)):

```stilt E0333:2
/// Applies `f` twice.
/// prop: |f: fn(i64) -> i64, x: i64| twice(f, x) == f(f(x))
fn twice(f: fn(i64) -> i64, x: i64) -> i64 { f(f(x)) }
```

A property can't perform `io`, because one that read a file or the clock could pass on one run and fail on the next. Its first call that performs `io` is E0510, *property that performs `io`*.

## Diagnostics

A **diagnostic** is an error, with a code such as `E0211`, or a warning, with a code such as `W0300`, at a file and a line. Each command reports them this way:

| Command | Reports | Exit status |
| --- | --- | --- |
| `check` | Every error and warning, and runs nothing | `0` if there are no errors, `1` otherwise |
| `run` | Every error and warning, then runs the program either way | `2` if there are errors, otherwise the program's own |
| `test` | Every error and warning, and runs the tests only when there are no errors | `0` if there are no errors and every test passes, `1` otherwise |

A program with warnings runs. Here the hole `?` is W0300, *hole*, and the program panics with the kind `hole` when it reaches it:

```stilt W0300:1 exit:101
fn damage(attack: i64, effectiveness: i64) -> i64 = ?

fn main() / io {
  print("the battle begins")
  print("{damage(8, 200)}")
}
```

```output
the battle begins
```

The compiler reports only **root causes**, so that one mistake gives one diagnostic ([Root causes](../../reference/18-errors.md#root-causes)). A name that doesn't resolve, or an expression that doesn't type-check, gets the **error type**, which fits everywhere and causes no further error. A body is checked in phases, and a later phase runs only when the earlier ones found nothing in that body ([Bodies and phases](../../reference/18-errors.md#bodies-and-phases)). So the misspelled `prase_hp` below is the only error, and the missing `try` before `parse_hp(a)` is reported once the name is fixed:

```stilt E0211:5
fn parse_hp(text: str) -> i64 / raise<str> { text.to_i64() else raise "not a number: {text}" }

fn total_hp(a: str, b: str) -> i64 / raise<str> {
  let x = parse_hp(a)
  x + prase_hp(b)
}
```

E0211 is *unknown name*. A file with a syntax error is read a declaration at a time, so a mistake in one function leaves the rest of the file checked ([Reading a file in parts](../../reference/18-errors.md#reading-a-file-in-parts)). `stilt show E0211` explains any code, with examples. With `--json`, `check` and `test` write each diagnostic as an object with its `code`, `file` and `line`. The compiler adds its message, its fixes, and what would fit in its place, such as `parse_hp` for `prase_hp`.

## Programs with errors

`run` runs a program even when it has errors. It reports the diagnostics first, then runs `main`. Each function, method or constant with an error is replaced by a panic of the kind `check-error`, which happens only if the code is reached. Everything else runs, and the run exits with status 2 however the program ends, so that no script takes it for a success ([Programs with errors](../../reference/04-programs.md#programs-with-errors)):

```stilt E0211:1 exit:2
fn average_hp(team: List<i64>) -> i64 { totl / team.len() }

fn main() / io {
  print("the battle begins")
  print("{average_hp([30, 34, 32])}")
}
```

```output
the battle begins
```

The panic report points at the name of the code with the error, here `average_hp` on line 1:

```text
panic: check-error: …
  at main.lt:1:4
```

An error in a function's body stops only that function, while an error in its signature stops its callers too, because they meet the error type through it ([program.meeting-the-error-type](../../reference/04-programs.md#program.meeting-the-error-type)). A syntax error in a function's body keeps its signature, so the rest of the file runs:

```stilt E0100:1 exit:2
fn damage(attack: i64) -> i64 { attack * }

fn bonus(attack: i64) -> i64 { attack + 2 }

fn main() / io {
  print("{bonus(8)}")
  print("{damage(8)}")
}
```

```output
10
```

`test` and `build` refuse a program with errors.

## The REPL

`stilt repl` evaluates what you type, one line at a time. It works in the scope of the program in the working directory: its module `main`, with its items, its imports and the prelude. An expression answers with its value and its type. A `let` answers with the type of each name it binds, and keeps the bindings for the inputs after it. When you edit and save the program's files, the next input sees the new code, and the bindings keep their values ([The REPL](../../reference/19-tools.md#the-repl)):

```text
$ stilt repl
> let embercat = Creature { name: "Embercat", element: Fire, hp: 30, attack: 8 }
embercat: Creature
> remaining(embercat.hp, 12)
18: i64
> [embercat][3]
panic: bounds: index 3 is out of bounds for a list of length 1
> embercat.name
"Embercat": str
```

An input is checked as a test body is, so it can print, and raise with `try`. A raise or a panic ends only that input, and `exit` or the end of the input ends the session. Declarations stay in the program's files, so an input that declares an item is refused, and so is a `var`, an assignment or an `assert`. `:module NAME` moves the session to another module, whose private items the next inputs see. An edit that changes a type that a binding's type names drops the binding, with a note, since its value has the old layout.

## The canonical format

Stilt has one syntax and one canonical format, which `stilt fmt` writes, and the formatter has no options. It indents by two spaces, and writes a block that holds one statement on one line when the line fits in 100 columns. A field whose value is a variable of the same name is written punned: `power: power` becomes `power` ([The canonical format](../../reference/03-syntax.md#the-canonical-format)). Where the source broke its lines doesn't matter. So the formatter turns this input:

```text
type Element = | Fire | Water | Plant

type Move = {
    name: str,
    element: Element,
    power: i64,
}

fn strongest(moves: List<Move>) -> i64 {
    var best = 0; for m in moves {
        best = best.max(m.power)
    }
    best
}

fn flame(power: i64) -> Move {
    Move { name: "Flame Pounce", element: Fire, power: power }
}
```

into this:

```stilt
type Element = | Fire | Water | Plant

type Move = { name: str, element: Element, power: i64 }

fn strongest(moves: List<Move>) -> i64 {
  var best = 0
  for m in moves { best = best.max(m.power) }
  best
}

fn flame(power: i64) -> Move { Move { name: "Flame Pounce", element: Fire, power } }
```

Every option of a formatter would make another canonical form, with noisier diffs. For the same reason, the format changes only in a January release ([versions.formatting-kept](../../reference/21-versions.md#versions.formatting-kept)).

## Packages and dependencies

A **package** is a directory with a manifest, `stilt.toml`, and its modules under `src/`. `stilt new arena` writes one, with a `main` and a test, and `stilt new --lib roster` writes a library. The manifest names the package and the packages it depends on ([Packages](../../reference/04-programs.md#packages)):

```toml
[package]
name = "arena"
edition = "2027"

[dependencies]
roster = { path = "../roster" }
json = { from = "github.com/someone/stilt-json", version = "1.4.0", hash = "b3:4f2a…", may = ["fs"] }
```

A manifest that isn't valid TOML, or holds a table or a key other than these, is E0600, *malformed manifest*. Each key of `[dependencies]` is the name that the dependency's own manifest gives it, or it is E0603, *dependency named unlike its package*, because there are no import aliases. Its value holds these keys:

| Key | Value |
| --- | --- |
| `path` | The directory that holds the dependency, for packages developed together |
| `from` | The git repository that holds it, as `HOST/PATH`, fetched from `https://HOST/PATH` |
| `version` | Its version, `MAJOR.MINOR.PATCH`, which is the repository's tag `vMAJOR.MINOR.PATCH` |
| `hash` | Its content hash, `b3:` and 64 hexadecimal digits |
| `may` | The effects it is granted, as a list of strings |

An entry holds `path` or `from`, not both. A dependency that can't be had, such as a `path` to no package, is E0601, *dependency that can't be fetched*.

**Fetched versions.** If an entry gives `from` alone, the next command fetches the repository's highest version, and writes `version` and `hash` into the entry. If it gives `from` and `version`, the command writes the `hash`. An entry with all three never changes: to move to another version, write the new `version` and remove the `hash`. Every command checks the content against the hash, and content that doesn't match is E0602, *content that doesn't match its hash* ([Fetched dependencies](../../reference/04-programs.md#fetched-dependencies)).

**Checked versions.** A version number must match the change in the package's API: its `pub` items, their signatures, and their facts that a `without` can name ([A package's API](../../reference/21-versions.md#a-packages-api)). Removing or changing any of them, or adding a method to a trait, needs a new major version. Any other addition, such as a new item, needs a new minor version, and an unchanged API needs only a new patch version. A version that understates its change is E0604, *version that understates its API change*. `stilt diff OLD NEW` shows what a new version needs:

```text
$ stilt diff ../roster-1.4.2 . --from 1.4.2
major  gains `div` in `roster.all`
minor  adds `roster.strongest`
needs a new major version: 1.4.2 → 2.0.0
```

**One version of each package.** When several manifests ask for one repository, the highest version asked for is selected. So two machines given the same manifests build the same program, with no lockfile. The versions asked for must share their major number, or the program has E0605, *versions that don't agree* ([Selecting versions](../../reference/21-versions.md#selecting-versions)).

**Modules of dependencies.** The module `main` of a dependency `json` is named `json`, and its module `decode` is named `json.decode`. A module can import from its own package, from `std` and from the packages its manifest names. A `use` of a module of a dependency's dependency is E0218, *package that isn't a dependency*, whose fix adds the entry ([Dependencies in a program](../../reference/04-programs.md#dependencies-in-a-program)).

**Granted effects.** A dependency can perform only the effects that its entry's `may` grants, and none without one. A grant names `io`, which covers everything a program can reach, or the capabilities below it that the dependency uses. For example, `may = ["console"]` grants a dependency that only prints ([Capabilities](05-errors.md#capabilities)). A dependency whose own code performs an effect that isn't granted is E0608, *effect that the manifest doesn't grant*, which offers the narrowest grant. The effects of a function that you pass to a dependency are yours, so they need no grant ([Granted effects](../../reference/04-programs.md#granted-effects)).

**No dependency code runs before the program.** Fetching, checking and building run none of a dependency's code, and a package has no build script. `stilt test` runs only the root package's own tests.

**Editions.** A package names its **edition**, a year, as `edition = "2027"`, and one that names none is of 2027, the only edition. Only an edition can break a program that an earlier release accepted, and each package of a program is read with its own edition. `stilt migrate` moves a package to the newest edition, and rewrites what that edition renames ([Editions](../../reference/04-programs.md#editions)):

```text
$ stilt migrate
arena: edition 2027, the newest
```

## Release builds

`stilt build` writes a debug build, which compiles in milliseconds and keeps every check. `stilt build --release` lowers the program to C and compiles it with clang, which takes longer and runs faster. Both builds mean the same, with the same output, exit status and panic report. A release build drops each check that verification proves can't fail ([Release builds](../../reference/20-builds.md#release-builds)).

A release build compiles a generic function once for each list of type arguments it is called with, so this `largest` is compiled for `i64` and for `str` ([Specialization](../../reference/20-builds.md#specialization)):

```stilt
fn largest<T: Ord>(xs: List<T>) -> T {
  var best = xs[0]
  for x in xs { if x > best { best = x } }
  best
}

fn main() / io { print("{largest([3, 9, 4])} {largest(["b", "a"])}") }
```

```output
9 b
```

`stilt show --release` prints what each function costs in the release build: the types it is compiled for, its reference-count operations, and the checks it keeps:

```text
$ stilt show --release main.largest largest.lt
fn largest<T: Ord>(xs: List<T>) -> T
  compiled for: T = i64, T = str
  references: 2 operations (line 3), no copy
  checks: 1 kept (bounds, line 2)
```

The bounds check stays, because `xs` could be empty.

`stilt run --profile` and `stilt test --profile` count how often each body, branch and loop of the program runs, and add the counts to a **profile**, `largest.profile` beside `largest.lt`. A release build reads it to tell clang which branches are likely, and it changes nothing the program does. A profile is text, kept and reviewed with the code, and a line that isn't of its form is E0610, *malformed profile* ([Profiles](../../reference/20-builds.md#profiles)).

## WebAssembly

`stilt build --target wasm32-wasip1` writes a WebAssembly module, which a WASI runtime such as wasmtime runs ([WebAssembly](../../reference/20-builds.md#webassembly)):

```text
$ stilt build --release --target wasm32-wasip1 -o arena.wasm arena/
$ wasmtime run --dir . arena.wasm
```

The module means what the program means on every target. It reaches only the directories that the runtime grants, and a path outside them raises `PermissionDenied`. Tasks and `std.par` run one after another, which gives the same results. A module has at most 4 GiB of memory, and WASI passes on only exit statuses below 126.

## Calling Stilt from C

A function written `pub extern fn` is **exported**: a C program calls it by its name. Its parameters and result are numbers or `bool`, which C sees as `int8_t` to `int64_t`, `uint8_t` to `uint64_t`, `float`, `double` and `bool`, and a result of `()` is `void` ([Exporting functions to C](../../reference/20-builds.md#exporting-functions-to-c)):

```stilt
/// How many steps the Collatz sequence takes from `n` down to 1.
pub extern fn collatz_steps(n: u64) -> i64 {
  var x = n
  var steps = 0
  while x > 1 {
    x = if x % 2 == 0 { x / 2 } else { 3 * x + 1 }
    steps += 1
  }
  steps
}
```

`stilt build --lib` writes a static library of the exported functions, with a C header that declares each one under its doc comment:

```text
$ stilt build --release --lib -o out/collatz collatz/
$ ls out
collatz.h  libcollatz.a
$ cc -o steps steps.c out/libcollatz.a
```

```c
// How many steps the Collatz sequence takes from `n` down to 1.
int64_t collatz_steps(uint64_t n);
```

An exported function takes no type, value or row parameter and no `inout` or `escaping` parameter. It performs no effect but `io`, because C couldn't see a `raise` or a handler. Each part of a signature that C can't take is E0352, *exported function C can't call*:

```stilt E0352:1
pub extern fn checksum(line: str) -> u32 { 0 }
```

The name must not clash with C: a C keyword, `main`, a name that POSIX declares, such as `read`, or a name with a reserved prefix, such as `_`, is E0352 too. Two exported functions with one name are E0219, *exported name used twice*. A panic in an exported function prints its report and ends the C program with status 101, so no panic crosses into C.

## Calling C

A function that a C library provides is declared with `extern fn` and no body, and called inside an `unsafe` block, whose reason says why the call is sound ([Foreign functions](../../reference/20-builds.md#foreign-functions)):

```stilt
use std.c

extern fn strlen(s: c.Str) -> u64

/// The length of `text` in bytes, as C counts them.
fn c_length(text: str) -> u64 {
  unsafe because "with_c_str ends s with a NUL, where strlen stops" {
    text.with_c_str(|s| strlen(s))
  }
}

fn main() / io { print("{c_length("Mossling")}") }
```

```output
8
```

A **foreign function** takes the types that an exported function takes, and two more from `std.c`: `c.Ptr<T>`, an address that C reads or writes, and `c.Str`, a string that ends with a NUL. It has no generics, no `inout` parameter and no effect but `io`. A type that C can't take, such as a `List`, is E0353, *type C can't take*:

```stilt E0353:1
extern fn crc32(crc: u64, buf: List<u8>, len: u32) -> u64

fn main() {}
```

**Unsafe operations.** Some operations are **unsafe**, such as calling a foreign function or reading through a `c.Ptr`. Each one must stand inside an `unsafe because "reason" { … }` block, or it is E0436, *unsafe operation outside `unsafe`*. A reason that is blank or interpolates is E0437, *`unsafe` with no reason* ([Unsafe code](../../reference/20-builds.md#unsafe-code)):

```stilt E0436:3
extern fn abs(n: i32) -> i32

fn distance(a: i32, b: i32) -> i32 { abs(a - b) }

fn main() {}
```

**Lending a buffer.** `xs.with_ptr(f)` calls `f` with the address of a list's first element, and keeps the list alive until `f` returns. `xs.with_mut_ptr(f)` lends an address that C can write through, and the list holds what C wrote when `f` returns. `s.with_c_str(f)` lends a copy of a string with a NUL at its end:

```stilt
use std.c

extern fn memset(dest: c.Ptr<u8>, ch: i32, count: u64) -> c.Ptr<u8>

fn main() / io {
  var buf: List<u8> = [1, 2, 3, 4]
  buf.with_mut_ptr(
    |p| unsafe because "memset writes 3 of buf's 4 bytes" { let _ = memset(p, 9, 3) },
  )
  print("{buf}")
}
```

```output
[9, 9, 9, 4]
```

**What C code may do.** A call of a C function counts as one that can panic, allocates and might not end, and that has every capability when it performs `io`, since nothing reads C code. A wrapper has those facts, and so has each of its callers, so `without alloc` rejects a call of `c_length`. A declaration that ends with a `without` clause says what its C code doesn't do, and its calls then add none of it. That statement is trusted, not checked, and `stilt show` says so at each call ([Foreign functions](../../reference/20-builds.md#c.effects)):

```stilt
extern fn labs(n: i64) -> i64 without panic, alloc, div

/// How far apart `a` and `b` are.
fn distance(a: i64, b: i64) -> i64 without alloc {
  unsafe because "labs takes any i64 but the least" { labs(a - b) }
}

fn main() / io { print("{distance(3, 10)}") }
```

```output
7
```

**Facts.** A function whose own code holds an `unsafe` block has the fact `unsafe`, and the C functions it calls are its fact `foreign`. A caller of that function inherits neither, so a safe wrapper keeps its callers safe. `stilt show` prints both, with each block's reason. `without unsafe` on a module or a function makes each `unsafe` block of its own code E0204 ([The facts of unsafe code](../../reference/20-builds.md#the-facts-of-unsafe-code)).

**Libraries.** `link` in the manifest's `[package]` names the C libraries that the foreign functions need, as `link = ["z"]`. A library that the system's loader doesn't find is E0611, *C library that isn't found*; checking looks for it without loading it, so none of its code runs until the program does. A dependency whose own code holds an `unsafe` block needs `unsafe` in its `may`, which `io` doesn't grant, or it is E0608. A program that links a library builds only for the machine's own target, and a build for another is E0612, *C libraries for another target* ([Packages that call C](../../reference/20-builds.md#packages-that-call-c)).

## Addresses and edits

Every declaration has an **address**, its module's name followed by its own, such as `main.remaining`, `main.Creature` or `main."a raise fails the test"`, and its body has one too, as `main.remaining/body`. A hash after it tells which version of the code you read: `main.remaining/body#b61c` ([Parts and addresses](../../reference/19-tools.md#parts-and-addresses)). The hash comes from the code's canonical text, so formatting a file never changes it. `stilt show --json` gives the address with its current hash:

```text
$ stilt show main.remaining --json
{…, "at": "main.remaining#d6f0", "text": "fn remaining(hp: i64, damage: i64) -> i64 { (hp - damage).max(0) }", "body": "main.remaining/body#b61c"}
```

`check` and `test` take edits addressed this way, apply them, and answer with the verdict on the edited program:

```text
$ stilt check --edit 'main.remaining/body#b61c' '{ if damage >= hp { 0 } else { hp - damage } }'
applied main.remaining/body#b61c -> #8cba
```

If an edit's hash isn't the code's current one, because the code changed since it was read, the edit is refused. Then no file changes, and the command exits with status 2 ([Edits](../../reference/19-tools.md#edits)). Each fix that `check --json` offers is written as such an edit.

## Pinned docs and copies

A doc describes what callers see, so a package pins each doc to its declaration's signature, in `docs.lock` beside `stilt.toml`. When a signature changes and its doc doesn't, the doc is **stale**, and `check` reports W0002, *stale doc*. `stilt fmt` and edits through `--edit` keep `docs.lock` up to date ([Pinned docs](../../reference/04-programs.md#pinned-docs)).

Two functions with the same body drift apart when one is fixed and the other isn't. Each copy of a body of at least 20 tokens, after the first, is W0302, *duplicate body*, at its function's name ([Duplicate bodies](../../reference/04-programs.md#duplicate-bodies)):

```stilt W0302:7
type Element = | Fire | Water | Plant

type Creature = { name: str, element: Element, hp: i64, attack: i64 }

fn strength(c: Creature) -> i64 { c.hp * 2 + c.attack * 3 + c.hp / 10 + 1 }

fn power(d: Creature) -> i64 { d.hp * 2 + d.attack * 3 + d.hp / 10 + 1 }
```

The names of parameters, the layout and the comments don't matter. When the two functions have the same signature, the fix replaces the later body with a call of the first, `{ strength(d) }`.

`stilt doc` writes a package's documentation as HTML: a page for each module, with its tier and each `pub` declaration's signature, doc, examples and facts ([Rendered documentation](../../reference/04-programs.md#rendered-documentation)).
