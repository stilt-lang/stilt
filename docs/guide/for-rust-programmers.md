# Stilt for Rust programmers

Here is the tour's `hit` function in Rust:

```rust
fn hit(attacker: &Creature, defender: &mut Creature) -> String {
    defender.hp = (defender.hp - attacker.attack).max(0);
    format!("{} hits {}. {} has {} HP left.", attacker.name, defender.name, defender.name, defender.hp)
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

Stilt has no references. `attacker` is a plain parameter, which behaves as the function's own copy, and `inout` takes the place of `&mut`, with no lifetime. A string literal interpolates any expression between braces. `/ io` says that `main` prints: a function's signature lists what it does to the outside world.

## At a glance

These are the Rust forms you know, with what Stilt writes instead:

| Rust | Stilt |
| --- | --- |
| `cargo new`, `run`, `test`, `build --release`, `check`, `fmt`, `doc` | `stilt new`, `run`, `test`, `build --release`, `check`, `fmt`, `doc` |
| rust-analyzer | `stilt lsp` |
| `Cargo.toml` | `stilt.toml` |
| `let`, `let mut` | `let`, `var` |
| `&T` | a parameter |
| `&mut T` | an `inout` parameter, passed as `f(inout x)` |
| moves, `Clone`, `Copy` | copies, which the compiler avoids where it can |
| `String` and `&str` | `str` |
| `Vec<T>`, `HashMap<K, V>` | `List<T>`, `Map<K, V>`, which keeps insertion order |
| `usize` lengths and indices | `i64` |
| `Result<T, E>` and `?` | `raise<E>` in the row, and `try` before each call that can raise |
| `Option<T>`, `unwrap_or` | `Option<T>`, `else` |
| `#[derive(PartialEq, Eq, Hash, Debug, …)]` | nothing to write |
| associated types | trait parameters |
| `mod`, `use a::b::Item` | a file is a module; `use std.fs`, then `fs.read` |
| `#[test]`, doctests, proptest | `test "name" { … }`, `/// ex:` lines, `/// prop:` lines |
| `macro_rules!` | `syntax` declarations, used as `name!(…)` |
| Rayon, `std::thread`, `Mutex<T>` | `std.par`, `std.task`, `sync.Shared<T>` |

## Values and copies

In Rust, a reference into a vector keeps the vector from changing while the reference lives:

```rust
let mut roster = vec!["Embercat", "Mossling"];
let first = &roster[0];
roster.push("Tidepup"); // error[E0502]: cannot borrow `roster` as mutable because it is also borrowed as immutable
println!("{first}");
```

In Stilt every binding holds a value. Assigning or passing a value makes an independent copy, so the same program compiles:

```stilt
fn main() / io {
  var roster = ["Embercat", "Mossling"]
  let first = roster[0]
  let saved = roster
  roster.push("Tidepup")
  print("{first} {saved} {roster}")
}
```

```output
Embercat ["Embercat", "Mossling"] ["Embercat", "Mossling", "Tidepup"]
```

The compiler keeps copies cheap: `saved` shares the list's storage with `roster` until `push` changes it ([how copies stay cheap](../../reference/rationale/05-values.md#value-semantics)). A caller can always keep using what it passed, so there are no move errors. The compiler infers which parameters a function **consumes**, by returning or storing them. When a call passes the last use of a value to one, the callee reuses its memory instead of copying it. `stilt show` prints which parameters each function consumes, and marks each call that can't reuse its argument because the caller uses it again ([Consumed parameters](07-modes.md#consumed-parameters)).

The **law of exclusivity** takes the place of the borrow checker. Two overlapping places passed `inout` to one call, as in `swap(inout xs[0], inout xs[1])`, are an error, as two `&mut` borrows of one vector are. So is changing a list while a `for` loop iterates over it ([The law of exclusivity](07-modes.md#the-law-of-exclusivity)).

The `advanced` tier adds views: windows into a string or a list that can't outlive the value they look into, still with no lifetimes written ([Views and iterators](11-views.md)).

## Numbers

Integer types are Rust's, `i8` to `i64`, `u8` to `u64`, with `f32` and `f64`. Lengths and indices are `i64`, and there is no `usize`. Nothing converts implicitly: `.to_f64()` and the other conversion methods take the place of `as`.

Integer overflow panics in every build, where Rust's release builds wrap by default. `+%`, `-%` and `*%` wrap on purpose, as `wrapping_add` does ([Integer arithmetic](02-values.md#integer-arithmetic)).

## Errors

Rust returns a `Result` and propagates it with `?`. Stilt puts the error type in the function's **row**, after `/`, and returns the plain value:

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

`try` marks each call that can raise, and a call without it doesn't compile. `catch` handles the error, and `Result.of` turns it into a `Result` where you want the value. A row holds one error type, so a function that meets two converts one, as `map_err` does ([Errors and effects](05-errors.md)).

A panic is a bug, as in Rust: an index out of range, a division by zero, an overflow. Nothing catches a panic.

## Variant types and `Option`

A variant type is Rust's `enum`, and `match` must cover every case, as in Rust:

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

A variant is named without its type, as `Hit(16)`, because the expected type decides which type it belongs to ([Variant types](04-declarations.md#variant-types)). A field read through an `Option` gives an `Option`, so `pounce.power` is Rust's `pounce.map(|m| m.power)`, and `else` is `unwrap_or` ([Fields through options](03-expressions.md#fields-through-options)).

## Traits and generics

Traits, `impl` blocks and bounds read as in Rust:

```stilt fragment
trait Label {
  fn label(self) -> str
}

impl Label for Move {
  fn label(self) -> str { "{self.name} ({self.power})" }
}

fn labels<T: Label>(xs: List<T>) -> List<str> { xs.map(|x| x.label()) }
```

No `derive` is written: a record, a variant type or a tuple gets `==`, ordering, hashing and printing from its parts, when they have them ([Structural impls](06-traits.md#structural-impls)). A call never names its type arguments, so there is no turbofish, and an annotation on the binding fixes a type where inference needs one. Bounds go on functions and impls only. What Rust calls an associated type is a trait parameter ([Trait parameters](13-trait-parameters.md#trait-parameters)).

## Tasks and parallel loops

`par.map`, `par.each`, `par.fold` and `par.both` of `std.par` play the part of Rayon, and give the result a sequential loop gives, on any number of cores. `task.spawn` starts a task, and `t.await()` waits for its value. A `with task.threads() { … }` block runs its tasks on threads and waits for all of them, as `std::thread::scope` does.

A task captures its values by copy, so it shares no place with the code that started it. State that tasks change together lives in a `sync.Shared<T>`, which plays the part of `Arc<Mutex<T>>`, and only a `when` block reaches its value. Cycles through `Shared` values are freed, where `Rc` cycles leak in Rust ([Effects, tasks and parallelism](17-effects.md)).

## Inferred facts and limits

Rust's signatures say who owns what, and leave out whether a function allocates or can panic. The compiler infers **facts** about every function, such as `alloc` when it allocates, `panic` when it can panic and `overflow` when its arithmetic can overflow. `stilt show` prints them with the operation behind each ([Ask what the compiler inferred](01-tour.md#ask-what-the-compiler-inferred)). A `without` clause turns facts into a **limit**, which the checker holds the body to. If you index a list in the tour's `fn damage(…) -> i64 without panic, alloc`, it stops compiling ([Limits](05-errors.md#limits)).

## Modules, packages and tests

A file is a module, and `pub` marks what other modules see. `use std.fs` imports the module, never an item, and code names `fs.read`; there are no import aliases and no re-exports. A package's dependencies are pinned by the hash of their contents, and a package has no build script ([Packages and dependencies](08-programs.md#packages-and-dependencies)).

Tests sit beside the code: a `test "name" { … }` block is a test, and a doc comment holds examples, `/// ex:` lines, and properties, `/// prop:` lines. `stilt test` runs a property on generated values ([Tests](08-programs.md#tests)).

A module's **tier**, `core`, `advanced`, `meta` or `systems`, is inferred from the features it uses, and `stilt show` prints it ([Module headers, tiers and limits](08-programs.md#module-headers-tiers-and-limits)). A statement whose value goes unused is an error, so `xs.sorted()` alone, which would drop a sorted copy, doesn't compile ([unused values](../../reference/08-expressions.md#expressions.unused-values)).

[Why Stilt is this way](10-design.md) gives the reasons for these choices, and the alternatives, Rust's among them, that each one turned down.
