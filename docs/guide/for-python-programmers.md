# Stilt for Python programmers

Here is the tour's `hit` function in Python:

```python
def hit(attacker: Creature, defender: Creature) -> str:
    defender.hp = max(defender.hp - attacker.attack, 0)
    return f"{attacker.name} hits {defender.name}. {defender.name} has {defender.hp} HP left."
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

The types in the signature are required, and checked before the program runs. A function changes its caller's value only through a parameter marked `inout`. The call says `inout mossling` too, so you can see that `mossling` may change. Every string literal is an f-string. Blocks are braces instead of indentation, and `/ io` says that `main` prints: a function's signature lists what it does to the outside world.

## At a glance

These are the Python forms you know, with what Stilt writes instead:

| Python | Stilt |
| --- | --- |
| `python main.py`, `pytest`, `black` | `stilt run`, `stilt test`, `stilt fmt` |
| `pyproject.toml`, `pip`, a virtualenv | `stilt.toml` |
| `x = 1` | `let x = 1`, which can't change, or `var x = 1`, which can |
| `def f(x: int) -> int:` | `fn f(x: i64) -> i64 { … }` |
| `f"{name} has {hp} HP"` | `"{name} has {hp} HP"` |
| `list`, `dict`, `set` | `List<T>`, `Map<K, V>`, `Set<T>`, each with one element type |
| `[x * 2 for x in xs if x > 0]` | `xs.filter(\|x\| x > 0).map(\|x\| x * 2)` |
| a `@dataclass` | a record, `type Point = { x: f64, y: f64 }` |
| a class's methods | functions in `impl Point { … }` |
| `Enum`, `isinstance` checks | variant types and `match` |
| `None` | `Option<T>`: `Some(x)` or `None` |
| `raise`, `try`/`except` | `raise<E>` in the row, `try` before each call that can raise, `catch` |
| `multiprocessing.Pool.map` | `par.map` |
| `if __name__ == "__main__":` | `fn main()` |

## Values and copies

A Python object is shared by every name that refers to it, so a change through one name shows through all of them:

```python
roster = ["Embercat", "Mossling"]
saved = roster
roster.append("Tidepup")
print(saved)  # ['Embercat', 'Mossling', 'Tidepup']
```

A Stilt value belongs to the name that holds it. Assigning it makes a copy, so `saved` keeps what it had:

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

The compiler keeps copies cheap: `saved` shares the list's storage until `push` changes `roster` ([how copies stay cheap](../../reference/rationale/05-values.md#value-semantics)). Only a `var` changes, and a method that changes its receiver takes `inout self` ([Parameter modes](07-modes.md)).

## Numbers

Python's `int` grows without limit. Stilt's integers have a fixed size: `i64` by default, with `i8` to `i64` and `u8` to `u64`, and `f32` and `f64` for floats. An integer operation whose result doesn't fit panics, and stops the program instead of giving a wrong number ([Integer arithmetic](02-values.md#integer-arithmetic)).

`/` on integers truncates toward zero, where Python's `//` rounds down, so they differ for negative numbers: `-7 / 2` is `-3`, and `-7 % 2` is `-1`; `div_euclid` and `rem_euclid` round down as Python does. In Stilt `//` begins a comment, so `a // 2` is `a` followed by a comment. A power is a method, `a.pow(2)`, not `a ** 2`. Nothing converts implicitly: if `hp` is an `i64`, `hp * 1.5` doesn't compile, and `hp.to_f64() * 1.5` does. Parsing text gives an `Option`, so `"forty".to_i64()` is `None` where `int("forty")` raises `ValueError`.

## Errors

In Python, any call can raise, and only the documentation says what. A Stilt function names what it raises in its **row**, after `/`:

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

A caller writes `try` before each call that can raise, or the program doesn't compile. `catch` plays the part of `except`, and its arms match the error's variants. `Result.of` gives the error as a value. A function with no row can't raise, and can't print either ([Errors and effects](05-errors.md)).

## Variant types and `Option`

A value of a variant type is exactly one of several cases, each with its own data. `match` must cover every case, where Python's `match` statement accepts a missing one:

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

A value that can be missing has the type `Option`, as the result of `find` does. The program must decide what a missing value means before it uses one. A field read through an `Option` gives an `Option`, and `else` gives a fallback when it is `None`, as `dict.get(key, default)` does ([Fields through options](03-expressions.md#fields-through-options), [Variant types](04-declarations.md#variant-types)).

## Traits and generics

Stilt has no classes and no inheritance. A record holds data, an `impl` block gives it methods, and a trait names methods that several types share:

```stilt fragment
trait Label {
  fn label(self) -> str
}

impl Label for Move {
  fn label(self) -> str { "{self.name} ({self.power})" }
}

fn labels<T: Label>(xs: List<T>) -> List<str> { xs.map(|x| x.label()) }
```

`labels` takes a list of any type that implements `Label`, as a function over a `Protocol` does, and the compiler checks each call. A record compares, hashes and prints itself field by field, with no `__eq__` or `__repr__` to write ([Structural impls](06-traits.md#structural-impls)).

## Tasks and parallel loops

`par.map` runs a function over a list on every core, with no processes to start and nothing to pickle. The function can't print or raise, so the result is the one a loop gives.

`task.spawn` starts a task, and `t.await()` waits for its value. A `with task.threads() { … }` block runs its tasks on threads, at the same time, and waits for all of them. A program prints the same under threads as when each task runs to its end in turn ([Effects, tasks and parallelism](17-effects.md)).

## Inferred facts and limits

The compiler infers **facts** about every function, such as `alloc` when it allocates, `panic` when it can panic and `overflow` when its arithmetic can overflow. `stilt show` prints them with the operation behind each ([Ask what the compiler inferred](01-tour.md#ask-what-the-compiler-inferred)). A `without` clause turns facts into a **limit**, which the checker holds the body to. If you index a list in the tour's `fn damage(…) -> i64 without panic, alloc`, it stops compiling ([Limits](05-errors.md#limits)).

## Modules, packages and tests

A file is a module. `use std.fs` imports the module, as `import os` does, and code names `fs.read`; there is no `from … import`. `pub` marks what other modules see ([Programs](08-programs.md)).

Tests sit beside the code: a `test "name" { … }` block is a test, and a doc comment holds examples, `/// ex:` lines, and properties, `/// prop:` lines. `stilt test` runs a property on generated values, as Hypothesis does ([Tests](08-programs.md#tests)).

Arguments are positional: there are no keyword arguments, default values or `*args` ([calls](../../reference/08-expressions.md#expressions.arguments)).
