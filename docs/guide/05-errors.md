# Errors and effects

A function's signature says whether it can fail and whether it touches the outside world. Here `attack` can fail, and `main` handles the failure:

```stilt
type Element = | Fire | Water | Plant

type Creature = { name: str, element: Element, hp: i64, attack: i64 }

/// The attack of `c`, which can't attack once it has fainted.
fn attack(c: Creature) -> i64 / raise<str> {
  if c.hp == 0 { raise "{c.name} has fainted" }
  c.attack
}

fn main() / io {
  let embercat = Creature { name: "Embercat", element: Fire, hp: 30, attack: 8 }
  let mossling = Creature { name: "Mossling", element: Plant, hp: 0, attack: 6 }
  for c in [embercat, mossling] {
    let power = try attack(c) catch e => {
      print("{e}, so it skips its turn")
      continue
    }
    print("{c.name} attacks for {power}")
  }
}
```

```output
Embercat attacks for 8
Mossling has fainted, so it skips its turn
```

The **effect row** after the `/` lists what a function does besides compute its result. `/ raise<str>` says that `attack` can fail with an error of type `str`, and `/ io` says that `main` prints. `raise` reports the error, `try` marks the call that can fail, and `catch` handles the error, so `main` raises nothing itself.

Stilt has no exceptions and no null. An error goes back to the caller, which marks it, then handles it or passes it on. A value that might be missing is an `Option`. A bug, such as an index out of range, **panics**: it stops the program, and nothing catches it. Some effects are never written: the compiler infers whether a function can panic or allocate, and a `without` clause rules either out.

## Effect rows

A row comes after the return type, or after the parameter list when there is none. It is written `/ x` for one element, or `/ {x, y}` for several. The core language has two kinds of element:

- `io`: the function reads or writes the outside world, such as the console, files or the clock.
- `raise<E>`: the function can fail with an error of type `E`.

The elements of a row are unordered, so `/ {io, raise<str>}` and `/ {raise<str>, io}` are the same row. A row holds each element once: a second `io` or a second `raise` is E0500, *repeated row element* ([Rows](../../reference/12-effects.md#effects.repeated-elements)).

The compiler infers the effects of each body, and they must fit the row. A call performs what its callee's row holds, so a call to `print` performs `io`. A function that prints without `/ io` is E0502, *effect that doesn't fit the row*:

```stilt E0502:2
fn announce(name: str) {
  print("{name} enters the arena")
  print("{name} bows")
}
```

The error is at the first call that performs `io`. The second `print` gets no error of its own, because adding `/ io` fixes both ([Inference](../../reference/12-effects.md#effects.missing-effects)).

A closure literal performs nothing where it is written. Its body's effects become part of its type, and happen each time it is called:

```stilt
fn announcer(name: str) -> fn() / io { || print("{name} enters the arena") }

fn main() / io {
  let announce = announcer("Tidepup")
  announce()
  announce()
}
```

```output
Tidepup enters the arena
Tidepup enters the arena
```

`announcer` itself performs nothing. Its `/ io` belongs to the function type it returns, because a row after a function type belongs to the innermost function type ([Function types](../../reference/10-declarations.md#declarations.function-type-rows)). Rows can also hold `async` and the effects you declare yourself, which [Effects, tasks and parallelism](17-effects.md) covers.

## Raising errors

`raise e` fails with the error `e`, which can be a value of any type. If the caller needs to tell failures apart, make the error a variant type with one case for each. Here `parse_element` reads an element from text:

```stilt
type Element = | Fire | Water | Plant

type ParseError = | Empty | Unknown(str)

fn parse_element(text: str) -> Element / raise<ParseError> {
  match text {
    "" => raise Empty
    "Fire" => Fire
    "Water" => Water
    "Plant" => Plant
    _ => raise Unknown(text)
  }
}

fn main() / {io, raise<ParseError>} {
  let element = try parse_element("Water")
  print("{element}")
}
```

```output
Water
```

`raise` has type `Never`, so it fits wherever a value is expected: in a `match` arm, as here, or after the `Option` fallback `else`, as in `text.to_i64() else raise NotANumber(text)` ([Raising and marking](../../reference/12-effects.md#effects.raise)). A `raise` needs no `try`, since it is visible already.

The compiler turns a raise into a value that the function returns, which the caller checks. Nothing unwinds the stack, and a call that doesn't raise costs nothing extra ([how raising is compiled](../../reference/rationale/12-effects.md#raising-and-marking)).

## Marking calls with `try`

Every call that can raise must be inside a `try`. `try` doesn't handle the error: it marks the call, and the error goes on to the caller, so the function around the `try` must have the `raise` in its row. The operand of `try` reaches as far right as it can, so one `try` at the start of an expression marks every call in it:

```stilt
type ParseError = | Empty | NotANumber(str)

fn parse_hp(text: str) -> i64 / raise<ParseError> {
  if text == "" { raise Empty }
  text.to_i64() else raise NotANumber(text)
}

fn team_hp(a: str, b: str) -> i64 / raise<ParseError> { try parse_hp(a) + parse_hp(b) }

fn main() / {io, raise<ParseError>} {
  let hp = try team_hp("30", "34")
  print("{hp}")
}
```

```output
64
```

This is Swift's `try`, not Rust's `?`. `try e` has the type and the effects of `e`, and changes no value ([Raising and marking](../../reference/12-effects.md#effects.marking)). A raising call without a `try` is E0505, *raising call without `try`*, and the compiler offers to insert one:

```stilt E0505:3
fn parse_hp(text: str) -> i64 / raise<str> { text.to_i64() else raise "not a number: {text}" }

fn double_hp(text: str) -> i64 / raise<str> { parse_hp(text) * 2 }
```

A call inside a closure counts too. In `xs.map(|x| parse_hp(x))`, the closure can raise, so the call to `map` can raise as well. Write `try xs.map(|x| parse_hp(x))`, which marks both calls. A `try` inside the closure leaves `map` unmarked:

```stilt E0505:3
fn parse_hp(text: str) -> i64 / raise<str> { text.to_i64() else raise "not a number: {text}" }

fn parse_all(xs: List<str>) -> List<i64> / raise<str> { xs.map(|x| try parse_hp(x)) }
```

A `try` with no raising call to mark is W0500, *`try` with nothing to mark*:

```stilt W0500:1
fn heal(hp: i64) -> i64 { try hp + 10 }
```

## Handling errors with `catch`

`try e catch …` handles the errors that `e` raises. The short form has one arm, `catch P => x`. The block form, `catch { … }`, takes arms as `match` does, guards included:

```stilt
type ParseError = | Empty | NotANumber(str)

fn parse_hp(text: str) -> i64 / raise<ParseError> {
  if text == "" { raise Empty }
  text.to_i64() else raise NotANumber(text)
}

fn status(name: str, hp: str) -> str {
  let n = try parse_hp(hp) catch {
    Empty => 0
    NotANumber(t) => return "{name}: {t} is not a number"
  }
  "{name} has {n} HP"
}

fn main() / io {
  print(status("Embercat", "30"))
  print(status("Mossling", ""))
  print(status("Tidepup", "lots"))
}
```

```output
Embercat has 30 HP
Mossling has 0 HP
Tidepup: lots is not a number
```

Three rules decide what `try e catch …` is ([Handling errors](../../reference/12-effects.md#effects.catch)):

- **Coverage.** The arms must cover every error that `e` can raise, as the arms of a `match` must cover its value.
- **Type.** Its type is the common type of `e` and the arms. An arm of type `Never`, such as the `return` above, fits any type.
- **Effects.** Its effects are those of `e` without the raise it handles, plus those of the arms. So `status` raises nothing, and has no row.

Arms that miss an error are E0329, *patterns that don't cover every value*, at the `try`. Here nothing handles `NotANumber`:

```stilt E0329:8
type ParseError = | Empty | NotANumber(str)

fn parse_hp(text: str) -> i64 / raise<ParseError> {
  if text == "" { raise Empty }
  text.to_i64() else raise NotANumber(text)
}

fn hp_or_zero(text: str) -> i64 { try parse_hp(text) catch Empty => 0 }
```

The arms aren't part of the operand. A raising call in an arm needs a `try` of its own, and an arm can raise again, with the same error type or another one. That raise goes to the caller:

```stilt
type ParseError = | Empty | NotANumber(str)

fn parse_hp(text: str) -> i64 / raise<ParseError> {
  if text == "" { raise Empty }
  text.to_i64() else raise NotANumber(text)
}

fn hp_or_default(text: str, default: str) -> i64 / raise<ParseError> {
  try parse_hp(text) catch {
    Empty => try parse_hp(default)
    e => raise e
  }
}
```

A `catch` belongs to the innermost `try` whose operand is still open, so in `try a() + try b() catch …` it handles only `b()` ([Attaching `catch`](../../reference/03-syntax.md#syntax.catch-attachment)). At run time, a raise goes to the innermost `try … catch` whose operand is running, also from inside a closure that the operand calls ([Handling errors](../../reference/12-effects.md#effects.innermost-catch)).

## Catch-alls

An arm without a guard whose pattern is `_` or a variable is a **catch-all**. A catch-all can drop an error by mistake, so it must do one of three things: raise, use its variable, or give a reason with `because` and a string literal before the `=>`:

```stilt
fn parse_hp(text: str) -> i64 / raise<str> { text.to_i64() else raise "not a number: {text}" }

fn hp_or_full(text: str) -> i64 { try parse_hp(text) catch _ because "a creature with no HP given starts at full health" => 30 }

fn main() / io {
  let hp = try parse_hp("lots") catch e => {
    print("skipped: {e}")
    0
  }
  print("{hp} {hp_or_full("")}")
}
```

```output
skipped: not a number: lots
0 30
```

The first catch-all uses `e`, and the second gives a reason. A catch-all that does none of the three is W0501, *catch-all without a reason*, at its pattern:

```stilt W0501:3
fn parse_hp(text: str) -> i64 / raise<str> { text.to_i64() else raise "not a number: {text}" }

fn hp_or_full(text: str) -> i64 { try parse_hp(text) catch _ => 30 }
```

The reason shows a reviewer that dropping the error was a choice. It is a string literal without interpolation, and only a catch-all takes one: `because` on any other arm is E0504, *reason on an arm that isn't a catch-all* ([Handling errors](../../reference/12-effects.md#effects.reasons-only-on-catch-alls)).

## One error type per row

A row holds at most one `raise<E>`. If a function calls code that fails with another error type, it wraps that error in its own, usually with `catch e => raise …`. Here `fs.read` raises `io.IoError`, and `load_hp` wraps it in a `LoadError`:

```stilt
use std.fs
use std.io

type LoadError = | Unreadable(io.IoError) | BadHp(str)

fn load_hp(path: str) -> i64 / {io, raise<LoadError>} {
  let text = try fs.read(path) catch e => raise Unreadable(e)
  text.trim().to_i64() else raise BadHp(text)
}

fn main() / io {
  let hp = try load_hp("embercat.txt") catch {
    Unreadable(e) => {
      print("can't read the file: {e}")
      30
    }
    BadHp(text) => {
      print("not a number of hit points: {text}")
      30
    }
  }
  print("Embercat has {hp} HP")
}
```

```output
can't read the file: NotFound("embercat.txt")
Embercat has 30 HP
```

A body that raises a type other than the one its row declares is E0503, *two error types*, at the first `raise` or call that does:

```stilt E0503:7
use std.fs
use std.io

type LoadError = | Unreadable(io.IoError) | BadHp(str)

fn load_hp(path: str) -> i64 / {io, raise<LoadError>} {
  let text = try fs.read(path)
  text.trim().to_i64() else raise BadHp(text)
}
```

Where no row is written, as in a closure's body or the operand of a `try … catch`, the first raise fixes the error type. A later raise of another type is E0503 too ([One error type](../../reference/12-effects.md#effects.one-error-type)). The same holds where branches or list elements are functions that raise different types ([Rows that meet](../../reference/12-effects.md#effects.rows-that-meet)).

## Errors that escape `main`

`main` can raise, if its error type implements `Show` ([Showing values](06-traits.md#showing-values)). An error that escapes `main` prints `error: ` and the error to stderr, and the program exits with status 1:

```stilt exit:1
use std.fs
use std.io

fn main() / {io, raise<io.IoError>} {
  let text = try fs.read("roster.txt")
  print(text)
}
```

```stderr
error: NotFound("roster.txt")
```

So a program that can't go on after an error needs no `catch` in `main`. [Exit statuses](08-programs.md#exit-statuses) lists the other ways a program ends.

## `Option` and `Result`

Two prelude types keep failure as data:

```stilt fragment
pub type Option<T> = | None | Some(T)
pub type Result<T, E> = | Ok(T) | Err(E)
```

An `Option` is a value that might be missing. The library returns one where a missing value is an ordinary answer, such as `get` on a list or a map, `find`, and `to_i64`. A `Result` holds the outcome of something that can fail, so you can keep it in a list or a field and look at it later. Looking up a creature in a roster gives an `Option`:

```stilt
type Element = | Fire | Water | Plant

type Creature = { name: str, element: Element, hp: i64, attack: i64 }

fn find(roster: List<Creature>, name: str) -> Creature / raise<str> {
  roster.find(|c| c.name == name) else raise "no creature called {name}"
}

fn main() / {io, raise<str>} {
  let roster = [
    Creature { name: "Embercat", element: Fire, hp: 30, attack: 8 },
    Creature { name: "Tidepup", element: Water, hp: 32, attack: 7 },
  ]
  let tidepup = roster.find(|c| c.name == "Tidepup")
  let mossling = roster.find(|c| c.name == "Mossling")
  print("{tidepup.hp} {mossling.hp}")
  let hps = ["Tidepup", "Mossling"].map(|n| Result.of(|| try find(roster, n).hp))
  print("{hps}")
  let first = try hps[0].get()
  print("Tidepup has {first} HP")
}
```

```output
Some(32) None
[Ok(32), Err("no creature called Mossling")]
Tidepup has 32 HP
```

`tidepup.hp` reads the field through the `Option`, and gives an `Option<i64>` ([Fields through options](03-expressions.md#fields-through-options)). In `find`, `else raise` turns a `None` into a raise. `Result.of` turns a raise into an `Err`, and `get` turns an `Err` back into a raise.

`try` acts only on raises, and never unwraps a `Result`. Every conversion between the two forms is written out:

| From | To | Write |
| --- | --- | --- |
| `Result<T, E>` | `T`, or a raise of `E` | `try r.get()` |
| A call that raises `E` | `Result<T, E>` | `Result.of(\|\| try f())` |
| `Option<T>` | `T`, or a raise | `o else raise e` |
| `Option<T>` | `Result<T, E>` | `o.ok_or(e)` |
| `Option<T>` or `Result<T, E>` | `T`, or a panic | `o.unwrap()` or `o.expect(msg)` |
| `Result<T, E>` | `Option<T>` or `Option<E>` | `r.ok()` or `r.err()` |

`try r` on a `Result` is still a `Result`, so where an `i64` is expected it is E0311, *mismatched types*. Write `try r.get()` instead:

```stilt E0311:1
fn hp(r: Result<i64, str>) -> i64 { try r }
```

If `try` unwrapped a `Result`, `try f()` would be ambiguous for an `f` that both raises and returns a `Result` ([Failure as data](../../reference/12-effects.md#effects.result)). Both types also have `map`, `Option` has `filter`, and `Result` has `map_err`, `is_ok` and `is_err` ([The standard library](09-library.md)). The `else` fallback and field reads work on an `Option` only, so read a `Result` through `.ok()` first.

## Effects that pass through

A function that takes a function as an argument performs whatever the argument performs, without saying so in its row. The argument's effects **pass through** to the caller, which marks and handles them as if it had made the calls itself:

```stilt
fn twice(hp: i64, hit: fn(i64) -> i64) -> i64 { hit(hit(hp)) }

fn checked(hp: i64) -> i64 / raise<str> {
  if hp == 0 { raise "already fainted" }
  (hp - 16).max(0)
}

fn main() / {io, raise<str>} {
  let quiet = twice(30, |hp| hp - 8)
  let loud = twice(30, |hp| {
    print("hit at {hp} HP")
    hp - 8
  })
  let left = try twice(34, checked)
  print("{quiet} {loud} {left}")
}
```

```output
hit at 30 HP
hit at 22 HP
14 14 2
```

`twice` has no row, yet the second call to it prints and the third can raise, so `main` marks that one with `try`. The library's functions that take functions work the same way: `map<U>(self, f: fn(T) -> U) -> List<U>` performs what `f` performs.

A row written on a function parameter lists the effects that the function takes charge of itself: a raise it catches, as [Handling an argument's failure](#handling-an-arguments-failure) shows, or `io`, which it then declares in its own row. Everything else passes through ([Parameters that pass effects through](../../reference/12-effects.md#effects.non-escaping-parameters)).

A parameter whose effects pass through is **non-escaping**: the function can only call it, or pass it on to another non-escaping parameter, directly or inside a closure literal. Keeping it in any other way, such as storing it in a record, returning it or binding it to a local, is E0508, *function parameter that escapes*. Its effects would outlive the call that brought them:

```stilt E0508:3
type Trigger = { name: str, on_faint: fn() / io }

fn trigger(name: str, on_faint: fn() / io) -> Trigger { Trigger { name, on_faint } }
```

The fix, which the error offers, marks the parameter `escaping`. An `escaping` parameter can be kept, and its row is then exactly the one written, so `on_faint` takes a function that performs at most `io`:

```stilt
type Trigger = { name: str, on_faint: fn() / io }

fn trigger(name: str, escaping on_faint: fn() / io) -> Trigger { Trigger { name, on_faint } }

fn main() / io {
  let t = trigger("Mossling", || print("Mossling has fainted"))
  t.on_faint()
}
```

```output
Mossling has fainted
```

Two other kinds of function parameter don't pass effects through: an `inout` one, which keeps its exact row, and a closure literal's, whose row is inferred from how the closure is used ([Closure parameters](../../reference/12-effects.md#effects.closure-parameters)).

## Row variables

If a function keeps a function argument and stays generic in its effects, it names them with a **row variable**: a lowercase name in its generic list, written in a row like an element. `compose` keeps both its arguments in the closure it returns:

```stilt
fn compose<A, B, C, e>(escaping f: fn(A) -> B / e, escaping g: fn(B) -> C / e) -> fn(A) -> C / e {
  |x| g(f(x))
}

fn main() / io {
  let hit_then_heal = compose(|hp: i64| hp - 8, |hp: i64| {
    print("healing at {hp} HP")
    hp + 5
  })
  print("{hit_then_heal(30)}")
}
```

```output
healing at 22 HP
27
```

Each use fills `e` with the rows of its arguments, here `io`. A row variable can sit beside other elements, as in `/ {io, e}`. Only functions declare row variables, and a written row holds at most one ([Rows](../../reference/12-effects.md#effects.row-variables)).

A non-escaping parameter passes its effects through already, so a row variable in its type is E0509, *row variable on a parameter that passes its effects through*. Remove `e` from both rows, and `hit_all` performs whatever `hit` performs:

```stilt E0509:1
fn hit_all<e>(hps: List<i64>, hit: fn(i64) -> i64 / e) -> List<i64> / e { hps.map(hit) }
```

## Function values with a larger row

A function value fits where a function type with a larger row is expected, so a pure function fits `fn() / io`. Where branches or the elements of a list literal are function values, their common type has the union of their rows, so `[rest, cheer]` below is a `List<fn() / io>`:

```stilt
fn rest() {}

fn cheer() / io { print("The crowd cheers") }

fn main() / io {
  let action: fn() / io = rest
  action()
  for action in [rest, cheer] { action() }
}
```

```output
The crowd cheers
```

The row grows only where a function value meets an expected type, such as an argument, an annotated `let` or a returned value ([Function values](../../reference/12-effects.md#effects.function-values)). A function type inside another type must match exactly, so a `List<fn()>` isn't a `List<fn() / io>`:

```stilt E0311:3
fn run_all(actions: List<fn() / io>) / io { for action in actions { action() } }

fn run_quiet(actions: List<fn()>) / io { run_all(actions) }
```

An `inout` argument must also have exactly its parameter's type, row included, because the callee could store a function with the larger row in it ([Parameter modes](07-modes.md)).

## Handling an argument's failure

A raise that passes through belongs to the caller. The function can't know its type, so it can't catch it. A call to a non-escaping parameter inside the operand of a `catch` is E0506, *`catch` around a failure that belongs to the caller*:

```stilt E0506:1
fn or_zero(read: fn() -> i64) -> i64 { try read() catch _ because "an unreadable value counts as zero" => 0 }
```

To catch the argument's failure, name it in the parameter's row. `raise<E>` there belongs to `or_zero`, with `E` a type parameter that each call fills with the argument's error type. The argument's other effects, such as `io`, still pass through:

```stilt
fn parse_hp(text: str) -> i64 / raise<str> { text.to_i64() else raise "not a number: {text}" }

fn or_zero<E>(read: fn() -> i64 / raise<E>) -> i64 { try read() catch _ because "an unreadable value counts as zero" => 0 }

fn main() / io {
  let a = or_zero(|| try parse_hp("30"))
  let b = or_zero(|| {
    print("reading lots")
    try parse_hp("lots")
  })
  print("{a} {b}")
}
```

```output
reading lots
30 0
```

`Result.of` is declared the same way: `of(f: fn() -> T / raise<E>) -> Result<T, E>`.

If a function passes its parameter on to one that handles failures, it must name the same error type in that parameter's row. Otherwise a caller could pass in any failure, and the inner function would take it for its own error type. Here `Result.of` handles a `LoadError`, but `wrap` lets any failure through, which is E0507, *failures passed on without their error type*:

```stilt E0507:3
type LoadError = | Missing(str)

fn wrap(read: fn() -> i64) -> Result<i64, LoadError> { Result.of(read) }
```

A caller could pass `|| raise true`, and `Result.of` would put a `bool` where a `LoadError` belongs. Writing the parameter as `read: fn() -> i64 / raise<LoadError>` fixes it. [Failures that pass through](../../reference/12-effects.md#effects.paired-row-variables) states these rules in full, for written and implicit row variables alike.

## Panics

A bug isn't an error for the caller to handle. A **panic** ends the program, or under `stilt test` only the test, and nothing catches it: `catch` handles raises only. The standard library raises or returns an `Option` where failure is an ordinary answer. It panics only for indexing, a few stated preconditions, such as the bounds of `slice`, and `unwrap` and `expect`, whose purpose is to panic. Every panic has a kind. These are the common ones:

| Kind | Caused by |
| --- | --- |
| `bounds` | An index or range out of bounds, in a list or a string |
| `missing-key` | Indexing a map that has no default with a missing key |
| `divide-by-zero` | Integer division or remainder by zero |
| `overflow` | Integer overflow (see [Integer arithmetic](02-values.md#integer-arithmetic)) |
| `unwrap` | `unwrap` or `expect` on a `None` or an `Err` |
| `assert` | A failed `assert` |
| `explicit` | `panic(msg)` |
| `unreachable` | `unreachable()` |
| `hole` | Reaching a typed hole `?` |

[Panics](../../reference/12-effects.md#effects.panic-kinds) lists the others, such as `deadlock`. `panic(msg)` and `unreachable()` have type `Never`. `unwrap()` and `expect(msg)` give the value inside a `Some` or an `Ok`, for code that knows it is there. A hole `?` stands for code not written yet, and checks with the warning W0300, *hole* (see [Declaring types](04-declarations.md)).

A panic writes two lines to stderr and exits with status 101. Everything the program printed before it reaches its stream first:

```stilt exit:101
fn main() / io {
  print("Round 1")
  panic("the battle has no winner")
}
```

```output
Round 1
```

```stderr
panic: explicit: "the battle has no winner"
  at main.lt:3:3
```

The first line names the kind and a detail. For `panic` and `expect`, the detail is the message, quoted. The second line gives the file, line and column where the operation that panicked starts: for `xs[i]`, the start of `xs`, and for a call, the start of its callee ([The panic report](../../reference/04-programs.md#program.panic-report)). `expect` names what the code took for granted, so its report says what went wrong:

```stilt exit:101
fn main() / io {
  let hp = "30".to_i64().expect("the hit points are a number")
  print("Embercat has {hp} HP")
  let attack = "eight".to_i64().expect("the attack is a number")
  print("Embercat attacks for {attack}")
}
```

```output
Embercat has 30 HP
```

```stderr
panic: unwrap: "the attack is a number"
  at main.lt:4:16
```

A stack overflow or running out of memory isn't a panic. It aborts the process with status 134 (see [Memory and recursion](08-programs.md#memory-and-recursion)).

## Implicit effects

Whether a function can panic or allocate is an effect too, but one you never write. The compiler infers these **implicit effects** from bodies: `panic`, `overflow`, `alloc`, `div`, for code that might not end, and `copy`, for a write that copies shared data. Writing `panic` or `alloc` in a row is E0501, *effect name as a row variable*:

```stilt E0501:1
fn announce(name: str) / {io, alloc} { print("{name} enters the arena") }
```

A function has an implicit effect when an operation in its body has it, including in a closure literal there. It also has every implicit effect of the functions it names, whether it calls them or uses them as values. A call through a function value adds nothing, because the effects were counted where the closure was written. So every panic belongs to the code whose text holds the operation ([Inferred facts](../../reference/15-facts.md#facts.inference)).

These operations add `panic` ([Panics](../../reference/12-effects.md#effects.panicking-operations)):

- An index, as `xs[i]` or `s[a..b]`.
- A read of `m[k]` on a map, even on a map with a default, which is known only at run time. A store `m[k] = v` adds nothing.
- Integer `/` and `%`, unless the divisor is an integer literal other than zero, as in `hp / 2`.
- `assert`, and a call of `panic`, `unreachable`, `unwrap`, `expect` or any other function that can panic.

[Proved checks](#proved-checks) shows the shapes of code in which an index, a division or a map read can't fail, so that it adds no `panic`. An operation whose only possible panic is an overflow, such as `+` on integers, adds `overflow` instead ([Overflow](#overflow)).

These operations add `alloc` ([Allocation](../../reference/15-facts.md#facts.allocation)):

- A list literal, a closure literal, and a string literal that interpolates.
- A record literal of a recursive type, and a variant of one that has a payload, such as `Node(l, r)` of `type Tree = | Leaf | Node(Tree, Tree)`.
- A write through an index, as `xs[i] = v`, since it copies the list when the list is shared.
- A `with`, a performance of an effect's operation, and a `for` over an iterator, which keep a handler, the rest of the performance and the loop's state.
- A function of the library's native code, but for a short list: the methods of numbers, the queries of `str`, `List` and `Map` such as `len`, `get` and `contains`, views, `std.math` and C pointers ([Natives](../../reference/15-facts.md#facts.native-allocation)). So `split`, `push`, `print`, `Shared.new`, every function of an iterator and the `show` of a number allocate.

Arithmetic, plain string literals, and records and tuples of other types allocate nothing. `stilt show` and the language server print a function's implicit effects after its signature, each with the line that causes it:

```text
fn hit(attacker: Creature, inout defender: Creature) -> str [consumes attacker, overflow, alloc]
```

No implicit effect is an error until a `without` clause limits it. They stay out of the types that callers check, so editing a body never breaks the type checking of its callers.

## Limits

A `without` clause turns an implicit effect into an error. Put it after a function's signature to limit that function, or in a module's header to limit every function of the module ([Module headers, tiers and limits](08-programs.md#module-headers-tiers-and-limits)). A limit also covers the functions that the code names, in any module. If code can't panic, it reads with `get`, which returns an `Option`, instead of indexing:

```stilt
module main
without panic

type Element = | Fire | Water | Plant

type Creature = { name: str, element: Element, hp: i64, attack: i64 }

fn leader(roster: List<Creature>) -> Option<str> { roster.get(0).name }

fn wins(winners: List<str>) -> Map<str, i64> {
  var counts: Map<str, i64> = Map.new()
  for w in winners {
    let n = counts.get(w) else 0
    counts[w] = n + 1
  }
  counts
}

fn main() / io {
  print("{leader([])}")
  print("{wins(["Embercat", "Tidepup", "Embercat"])}")
}
```

```output
None
{"Embercat": 2, "Tidepup": 1}
```

Each operation beyond a limit is E0204, *fact beyond a `without` limit*, and so is each call of a function that goes beyond it:

```stilt E0204:4 E0204:6
module main
without panic

fn first(roster: List<str>) -> str { roster[0] }

fn share(damage: i64, targets: i64) -> i64 { damage / targets }
```

A function's own clause works the same way. Here `List.new` and `push` allocate:

```stilt E0204:2 E0204:3
fn damages(n: i64) -> List<i64> without alloc {
  var out = List.new()
  for i in 0..n { out.push(i * 8) }
  out
}
```

A function limited by `without panic` counts as one that can't panic wherever it is named. Its own panics are errors where they are written, and its callers get none. The same holds for every limit ([Limits](../../reference/15-facts.md#facts.without)). A few things stay outside the limits:

- **Tests.** Test bodies, doc examples and properties are exempt, so the tests of a module under `without panic` can use `assert`.
- **Overflow.** `without panic` doesn't rule out overflow, so sums and counters need no special form. `without overflow` rules it out, and `without panic, overflow` means no panic at all, but for one:
- **Deadlock.** A `when` reached through a function value or a handler, on a value that a `when` around it already holds, panics with the kind `deadlock` ([Shared state](17-effects.md#shared-state)), which no limit sees.
- **Callbacks.** A callback's panics and allocations belong to the code that wrote it. So limited code can call a function value it is given, and `fold` keeps a limit whatever callback it gets.
- **Aborts.** A stack overflow or running out of memory still aborts the process.

### Proved checks

Some checks can't fail, and `stilt check` proves them by reading each body alone. A proved check adds no `panic`, so code under `without panic` can still index, divide and read a map in four shapes:

- A **range loop** proves `xs[i]` in the body of `for i in 0..xs.len()`, if the body doesn't change the length of `xs`.
- A **guard** proves `xs[i]` under tests that give `i >= 0` and `i < xs.len()`. `!xs.is_empty()` proves `xs[0]`.
- A **divisor** proves `n / d` if `d` is a literal other than zero, or a test gives `d != 0`, `d > 0` or `d < 0`.
- A **key** proves `m[k]` under `if m.contains(k)`, or after `m[k] = v`.

Nothing between the test and the operation can change the index, the divisor, the key or the length of the list. [The rules of acceptance](../../reference/15-facts.md#facts.rules-of-acceptance) give each shape exactly. Each of these functions checks:

```stilt fragment
fn total(hps: List<i64>) -> i64 without panic {
  var s = 0
  for i in 0..hps.len() { s += hps[i] }
  s
}

fn at(hps: List<i64>, i: i64) -> i64 without panic {
  if i < 0 || i >= hps.len() { return 0 }
  hps[i]
}

fn average(total: i64, count: i64) -> i64 without panic {
  if count == 0 { 0 } else { total / count }
}

fn wins(winners: List<str>) -> Map<str, i64> without panic {
  var m: Map<str, i64> = Map.new()
  for w in winners {
    if !m.contains(w) { m[w] = 0 }
    m[w] += 1
  }
  m
}
```

`stilt show` prints `proved bounds by a range loop` and the like where each panic would have been. An index that no rule proves is E0204, and the message names the closest rule and what it needs. Here the first index gets help that a range loop needs it to end at `hps.len()`. The second gets help that a guard needs a test that gives `i >= 0`, since a negative `i` passes `i < hps.len()`:

```stilt E0204:3 E0204:8
fn total_to(hps: List<i64>, n: i64) -> i64 without panic {
  var s = 0
  for i in 0..n { s += hps[i] }
  s
}

fn at(hps: List<i64>, i: i64) -> i64 without panic {
  if i < hps.len() { hps[i] } else { 0 }
}
```

If an index fits no shape, such as `rows[i][j]` or `cells[y * n + x]`, rewrite it into one, or read through `get`. Release builds prove more checks and drop them, but that changes nothing `check` accepts ([Verification](../../reference/15-facts.md#facts.what-proofs-change)).

### Updates in place

A write through an index allocates, since the list might be shared, and the write then copies it. Under `without alloc`, a function holds the **own storage** of its list parameters, so it writes them in place. A `var` that takes such a list at its last use holds it too:

```stilt
fn heal_all(hps: List<i64>) -> List<i64> without alloc {
  var out = hps
  for i in 0..out.len() { out[i] += 5 }
  out
}

fn faint_first(inout hps: List<i64>) without alloc { hps[0] = 0 }

fn main() / io {
  var team = [30, 34, 32]
  faint_first(inout team)
  let before = [20, 25]
  let after = heal_all(before)
  print("{team} {before} {after}")
}
```

```output
[0, 34, 32] [20, 25] [25, 30]
```

The caller keeps value semantics. `main` uses `before` after the call, so the call copies it, in `main`, which has no limit. A caller under `without alloc` must pass a list that nothing else uses, such as its own parameter at its last use, or the argument is E0204. A `var` holds its own storage at a write only if every assignment that may come before the write gives it some: an `if` that may skip `out = hps`, or an assignment later in a loop's body, which comes before the write on the next turn, counts too ([Own storage](../../reference/15-facts.md#facts.own-storage)). A write to a field of an element, as `ps[i].x += 1`, is in place too, if the elements are plain data. Numbers, `bool`, and records and tuples made only of them are plain data ([Updates in place](../../reference/15-facts.md#facts.writes-in-place)).

### Overflow

`overflow` is the implicit effect of integer operations that can overflow: `+`, `-` and `*` and their compound assignments, negation, signed division, shifts, and integer methods such as `abs` and `pow` ([Overflow](../../reference/12-effects.md#effects.overflow-effect)). The wrapping operators `+%`, `-%` and `*%`, and float arithmetic, don't overflow. Code under `without panic, overflow` can't panic at all, except with `deadlock` (see [Shared state](17-effects.md#shared-state)):

```stilt
fn strongest(attacks: List<i64>) -> i64 without panic, overflow {
  var best = 0
  for a in attacks {
    if a > best { best = a }
  }
  best
}

fn main() / io { print("{strongest([8, 6, 7])}") }
```

```output
8
```

Each operation that can overflow is E0204 under the limit, and so is each call of a function that can:

```stilt E0204:2
fn next_round(round: i64) -> i64 without overflow {
  round + 1
}
```

### Termination

`div` is the implicit effect of code that might not end: a `loop`, a `while` that isn't a counting loop, recursion that doesn't shrink, and a call through a stored function value, such as one in a field. A `for` loop adds nothing, since it always ends. Neither does a call through a parameter that isn't `escaping`, whose argument counts where it is written. `without panic, div` means **total**: the code ends without a panic, unless it overflows an integer, the stack or memory ([Termination](../../reference/15-facts.md#facts.div)).

Recursion ends when each call of the function to itself passes, at the same parameter, a **strict part** of it: a part reached through a field, a tuple element or a variant's payload. A tournament bracket shrinks at each round:

```stilt
type Bracket = | Seed(str) | Round(Bracket, Bracket)

fn entrants(b: Bracket) -> i64 without panic, div {
  match b {
    Seed(_) => 1
    Round(l, r) => entrants(l) + entrants(r)
  }
}

fn main() / io {
  let b = Round(Round(Seed("Embercat"), Seed("Mossling")), Seed("Tidepup"))
  print("{entrants(b)}")
}
```

```output
3
```

Two more shapes end ([Counting loops](../../reference/15-facts.md#facts.counting-loops), [Shrinking recursion](../../reference/15-facts.md#facts.shrinking-recursion)):

- A **counting loop** is a `while` that compares a `var`, its counter, with a bound by `<`, `<=`, `>` or `>=`. Its own block steps the counter toward the bound, as `i += 1` does for `i < n`.
- **Shrinking recursion** passes `n - 1`, or `n` minus another positive amount, at each self-call, under a test that gives `n > b` or `n >= b`. Growing toward a bound works the same way.

Both of these end under the limit:

```stilt fragment
fn count(n: i64) -> i64 without div {
  if n > 0 { 1 + count(n - 1) } else { 0 }
}

fn count_down(n: i64) -> i64 without div {
  var i = n
  while i > 0 { i -= 1 }
  i
}
```

Recursion that doesn't shrink, mutual recursion, and a `while` that isn't a counting loop are E0204 under the limit, even when they end. Halving passes no `n - 1`, and `!=` isn't a comparison that a counting loop uses:

```stilt E0204:2 E0204:7
fn rounds(n: i64) -> i64 without div {
  if n <= 1 { 0 } else { 1 + rounds(n / 2) }
}

fn count_to_zero(n: i64) -> i64 without div {
  var i = n
  while i != 0 { i -= 1 }
  i
}
```

The test matters too: `if n == 0 { 0 } else { count(n - 1) }` doesn't shrink, since `count(-1)` never ends.

### Copies

A write to a `var` or an `inout` parameter while a copy of it lasts copies the shared value, and so does a write inside a copy of another binding that a `var` holds, as its value or in a field or element of it, while that binding reads it afterwards: `var ys = xs` followed by `ys.push(1)` and then a read of `xs`. An `inout` parameter is read afterwards by the caller it goes back to, and a captured variable by the closure's next call, so `var ys = xs` followed by `ys.push(1)` copies there too. A copy of `x` lasts across `x = x.next`, since the new value is part of what the copy holds, and across `x = y` when `y` holds a copy of `x`. A copy also lasts in whatever a call may store it in, as its types tell: `ls.push(b)` keeps `b` in `ls`, and `xs.get(0)` may keep part of a `List<List<i64>>` in its result, so after `{ let b = xs; ls.push(b) }`, a write to `xs` copies while `ls` lasts ([modes.call-stores](../../reference/13-modes.md#modes.call-stores)). A handle's value counts as well: a `when` that lets a copy of its value outlive it, as `when a { a }` does, copies there, since a later `when` anywhere may write the value, and so does `Shared.new(xs)` when `xs` is read afterwards ([modes.handles](../../reference/13-modes.md#modes.handles)). What counts is every path the code may take: a copy made at the end of a loop's turn lasts into the next turn, and an assignment that a `break`, a raise or a branch may skip doesn't end a copy. `stilt show` marks such a write `shared` (see [Parameter modes](07-modes.md)). That is ordinary value semantics, and nothing warns about it. If code must not copy, `without copy` makes each such write E0204. Fresh values stay within the limit:

```stilt E0204:4
fn grow(hps: List<i64>) -> List<i64> without copy {
  var ys = hps
  let before = ys
  ys.push(1)
  before
}

fn fresh(hp: i64) -> List<i64> without copy {
  var ys = [hp]
  ys.push(hp + 1)
  ys
}
```

`overflow`, `div` and `copy` are limits only after `without` ([Copies](../../reference/15-facts.md#facts.without-copy)). Anywhere else they are ordinary names.

### Capabilities

`io` says that a function reaches the world, but not which part of it. Below it, eight **capabilities** are inferred from the natives a function reaches, as implicit effects are: `fs` for `std.fs`, `net` for `std.net` and `std.http`, `clock` for `std.clock`, `env` for `std.cli`, `console` for `print`, `eprint` and the console functions of `std.io`, `rand` for `random.entropy`, `spawn` for starting tasks, and `exec` for `std.process`. Each is a limit of `without`:

```stilt E0204:8
use std.fs
use std.clock

fn stamp(line: str) -> str / io { "{clock.unix_ms()} {line}" }

fn report(line: str) / io without fs {
  print(stamp(line))
  if fs.exists("battle.log") { print("logged") }
}
```

`report` prints and reads the clock, which `without fs` allows, but `fs.exists` reaches the file system. A callback's capabilities belong to the code that wrote it, so `without fs` promises that the code's own source reaches no file ([Capabilities](../../reference/15-facts.md#facts.capabilities)). Capabilities are never written in a row: a signature says `io`. `stilt show` prints them after the implicit effects, as `io: fs, clock`, and a manifest grants each dependency the ones it can use ([Packages and dependencies](08-programs.md#packages-and-dependencies)).
