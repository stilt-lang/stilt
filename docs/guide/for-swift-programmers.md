# Stilt for Swift programmers

Here is the tour's `hit` function in Swift:

```swift
func hit(_ attacker: Creature, _ defender: inout Creature) -> String {
    defender.hp = max(defender.hp - attacker.attack, 0)
    return "\(attacker.name) hits \(defender.name). \(defender.name) has \(defender.hp) HP left."
}
```

And here it is in Stilt:

```stilt
type Element = | Fire | Water | Plant

type Creature = { name: str, element: Element, hp: i64, attack: i64 }

fn hit(attacker: Creature, inout defender: Creature) -> str {
  defender.hp = (defender.hp - attacker.attack).max(0)
  "{attacker.name} hits {defender.name}. {defender.name} has {defender.hp} HP left."
}

fn main() / io {
  let embercat = Creature { name: "Embercat", element: Fire, hp: 30, attack: 8 }
  var mossling = Creature { name: "Mossling", element: Plant, hp: 34, attack: 6 }
  print(hit(embercat, inout mossling))
}
```

```output
Embercat hits Mossling. Mossling has 26 HP left.
```

Much carries over: `let` and `var`, structs as values, `inout`. The call writes `inout mossling` where Swift writes `&mossling`. Arguments have no labels, and a string interpolates with `{…}` in place of `\(…)`. `/ io` says that `main` prints: a function's signature lists what it does to the outside world.

## At a glance

These are the Swift forms you know, with what Stilt writes instead:

| Swift | Stilt |
| --- | --- |
| `swift package init`, `swift run`, `swift test`, `swift build -c release` | `stilt new`, `stilt run`, `stilt test`, `stilt build --release` |
| `Package.swift` | `stilt.toml` |
| `let`, `var` | `let`, `var` |
| `struct` | a record, `type Point = { x: f64, y: f64 }` |
| `class` | none |
| `enum` with associated values | a variant type, `type Turn = \| Hit(damage: i64) \| Miss` |
| `protocol`, `extension Type: Protocol` | `trait`, `impl Trait for Type` |
| `mutating func` | a method that takes `inout self` |
| `inout` and `&x` | `inout` in the signature and `inout x` at the call |
| `Optional`, `?.`, `??`, `guard let … else` | `Option`, fields read through it, `else`, `let … else` |
| `throws(E)`, `try`, `do`/`catch` | `raise<E>` in the row, `try`, `catch` |
| `async`/`await`, task groups | `task.spawn` and `t.await()`, in `with task.threads()` |
| actors | `sync.Shared<T>`, reached with `when` |
| `"\(x)"` | `"{x}"` |

## Values and copies

Swift's arrays and structs are values, and Stilt's values work the same way. The difference is that every Stilt type is a value: there are no classes, so no value shares state through a reference that it holds:

```stilt
fn main() / io {
  var roster = ["Embercat", "Mossling"]
  let saved = roster
  roster.push("Tidepup")
  print("{saved} {roster}")
}
```

```output
["Embercat", "Mossling"] ["Embercat", "Mossling", "Tidepup"]
```

As in Swift, `saved` shares the list's storage until `push` changes `roster` ([how copies stay cheap](../../reference/rationale/05-values.md#value-semantics)). Stilt has Swift's law of exclusivity, checked when the program compiles. Two overlapping `inout` arguments of one call, as in `swap(inout xs[0], inout xs[1])`, don't compile ([Parameter modes](07-modes.md)).

With no classes, there are no reference cycles to break with `weak`. The compiler also infers which parameters a function consumes, and reuses an argument's memory when the call passes its last use ([Consumed parameters](07-modes.md#consumed-parameters)).

## Numbers

The number types are Swift's sized ones, with shorter names: `i64` is `Int64`, `u8` is `UInt8` and `f64` is `Double`. Lengths and indices are `i64`. As in Swift, nothing converts implicitly, and integer overflow stops the program. `+%`, `-%` and `*%` wrap, as `&+`, `&-` and `&*` do ([Integer arithmetic](02-values.md#integer-arithmetic)).

## Errors

Swift's typed throws, `throws(HpError)`, name one error type. A Stilt function always names its error type, in its **row**, after `/`:

```stilt
type HpError = | NotANumber(text: str) | NotPositive(hp: i64)

/// The hit points written in `text`.
fn parse_hp(text: str) -> i64 / raise<HpError> {
  let hp = text.to_i64() else raise NotANumber(text)
  if hp <= 0 { raise NotPositive(hp) }
  hp
}

fn main() / io {
  let hp = try parse_hp("x") catch {
    NotANumber(_) => 1
    NotPositive(_) => 1
  }
  print("{hp} {Result.of(|| try parse_hp("30"))} {Result.of(|| try parse_hp("-5"))}")
}
```

```output
1 Ok(30) Err(NotPositive(-5))
```

`try` marks each call that can raise, as in Swift. `catch` comes after the call it handles, with no `do` block, and its arms match the error's variants. `Result.of` plays the part of `Result { try … }` ([Errors and effects](05-errors.md)).

## Variant types and `Option`

A variant type is an `enum` with associated values, and `match` is an exhaustive `switch`:

```stilt
type Element = | Fire | Water | Plant

type Move = { name: str, element: Element, power: i64 }

/// What happened on one turn of a battle.
type Turn = | Hit(damage: i64) | Miss

fn main() / io {
  for turn in [Hit(16), Miss] {
    print(match turn {
      Hit(damage) => "hit for {damage}"
      Miss => "missed"
    })
  }
  let moves = [Move { name: "Flame Pounce", element: Fire, power: 40 }]
  let pounce = moves.find(|m| m.name == "Flame Pounce")
  let jet = moves.find(|m| m.name == "Bubble Jet")
  print("{pounce.power else 0} {jet.power else 0}")
}
```

```output
hit for 16
missed
40 0
```

A variant is named without a leading dot, as `Hit(16)`. A field read through an `Option` gives an `Option`, so `pounce.power` reads as `pounce?.power` does, with no `?`, and `else` is `??`. `let x = … else return` is `guard let` ([Fields through options](03-expressions.md#fields-through-options), [`let` and let-else](04-declarations.md#let-and-let-else)). Swift's `if let x = maybe` is `if let Some(x) = maybe`: the pattern names the variant, and `if let x = maybe` binds the `Option` itself, which the compiler warns about (W0303).

## Traits and generics

A trait is a protocol, and `impl Label for Move` adds a conformance, as an extension does:

```stilt fragment
trait Label {
  fn label(self) -> str
}

impl Label for Move {
  fn label(self) -> str { "{self.name} ({self.power})" }
}

fn labels<T: Label>(xs: List<T>) -> List<str> { xs.map(|x| x.label()) }
```

A record, a variant type or a tuple gets `==`, ordering, hashing and printing from its parts. Swift synthesizes `Equatable` and `Hashable` too, but only for a declared conformance ([Structural impls](06-traits.md#structural-impls)). A method has one definition for each type, so there is no overloading.

## Tasks and parallel loops

`task.spawn` starts a task, and `t.await()` waits for its value. A `with task.threads() { … }` block runs its tasks on threads and waits for all of them before it ends, as a task group does. `par.map` runs a function over a list on every core.

A task captures its values by copy. State that tasks change together lives in a `sync.Shared<T>`, and only a `when` block reaches its value, as only an actor's own code reaches its state. A program prints the same under threads as when each task runs to its end in turn ([Effects, tasks and parallelism](17-effects.md)).

## Inferred facts and limits

The compiler infers **facts** about every function, such as `alloc` when it allocates, `panic` when it can panic and `overflow` when its arithmetic can overflow. `stilt show` prints them with the operation behind each, and `stilt show --release` prints the reference counts and checks that the release build keeps ([Ask what the compiler inferred](01-tour.md#ask-what-the-compiler-inferred)). A `without` clause turns facts into a **limit**, which the checker holds the body to. If you index a list in the tour's `fn damage(…) -> i64 without panic, alloc`, it stops compiling ([Limits](05-errors.md#limits)).

## Modules, packages and tests

A file is a module, where a Swift module is a whole target. `pub` marks what other modules see, and everything else is private to the file. `use std.fs` imports the module, and code names `fs.read` ([Programs](08-programs.md)).

Tests sit beside the code: a `test "name" { … }` block is a test, and a doc comment holds examples, `/// ex:` lines, and properties, `/// prop:` lines. `stilt test` runs a property on generated values ([Tests](08-programs.md#tests)).
