# Stilt for TypeScript programmers

Here is the tour's `hit` function in TypeScript:

```typescript
function hit(attacker: Creature, defender: Creature): string {
  defender.hp = Math.max(defender.hp - attacker.attack, 0);
  return `${attacker.name} hits ${defender.name}. ${defender.name} has ${defender.hp} HP left.`;
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

A function changes its caller's value only through a parameter marked `inout`. The call says `inout mossling` too, so you can see that `mossling` may change. Every string literal is a template string, with `{…}` in place of `${…}`. `/ io` says that `main` prints: a function's signature lists what it does to the outside world. A program whose types don't check doesn't run.

## At a glance

These are the TypeScript forms you know, with what Stilt writes instead:

| TypeScript | Stilt |
| --- | --- |
| `npm init`, `tsc`, `node`, `vitest`, `prettier` | `stilt new`, `stilt check`, `stilt run`, `stilt test`, `stilt fmt` |
| `package.json`, `package-lock.json` | `stilt.toml` |
| `const`, `let` | `let`, which can't change, `var`, which can |
| `` `${a} and ${b}` `` | `"{a} and {b}"` |
| `number` | `i64`, `f64` and the other number types |
| `T[]`, `Map<K, V>` | `List<T>`, `Map<K, V>` |
| `interface` or `type` of an object | a record, `type Point = { x: f64, y: f64 }` |
| a class's methods | functions in `impl Point { … }` |
| discriminated unions and `switch (x.kind)` | variant types and `match` |
| `undefined`, `null`, `?.`, `??` | `Option<T>`, fields read through it, and `else` |
| `throw`, `try`/`catch` | `raise<E>` in the row, `try` before each call that can raise, `catch` |
| `async`/`await`, `Promise.all` | `task.spawn` and `t.await()`, and `par.map` |
| `any`, `as` | none: a conversion is a method, such as `to_f64()` |

## Values and copies

A TypeScript object or array is shared by every name that refers to it, so a change through one name shows through all of them:

```typescript
const roster = ["Embercat", "Mossling"];
const saved = roster;
roster.push("Tidepup");
console.log(saved); // ["Embercat", "Mossling", "Tidepup"]
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

The compiler keeps copies cheap: `saved` shares the list's storage until `push` changes `roster` ([how copies stay cheap](../../reference/rationale/05-values.md#value-semantics)). A `let` can't change at all, its contents included, where `const` only fixes the binding. A function changes its caller's value only through `inout` ([Parameter modes](07-modes.md)).

## Numbers

TypeScript's `number` is a 64-bit float, so integers past 2⁵³ lose their last digits, and `7 / 2` is `3.5`. Stilt has integer types, `i64` by default, and float types, `f64` by default, and nothing converts between them implicitly. So `9007199254740993 + 1` is `9007199254740994`, and `7 / 2` is `3`, since integer `/` truncates toward zero. `7.0 / 2.0` is `3.5`.

An integer operation whose result doesn't fit panics instead of giving a wrong number ([Integer arithmetic](02-values.md#integer-arithmetic)). Parsing gives an `Option`: `"42".to_i64()` is `Some(42)`, and `"42px".to_i64()` is `None`, where `parseInt` gives `42`.

## Errors

A TypeScript function can throw anything, and nothing in its type says so. A Stilt function names what it raises in its **row**, after `/`:

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

A caller writes `try` before each call that can raise, or the program doesn't compile. The error has a type, so `catch` knows every case, with no `instanceof`. `Result.of` gives the error as a value ([Errors and effects](05-errors.md)).

## Variant types and `Option`

A discriminated union is a variant type, with a case name in place of the `kind` field, and `match` must cover every case:

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

There is no `undefined` and no `null`. A value that can be missing has the type `Option`, as the result of `find` does. A field read through an `Option` gives an `Option`, so `pounce.power` reads as `pounce?.power` does, and `else` gives the fallback that `??` would. Where an `i64` is expected, `jet.power` alone is a type error ([Fields through options](03-expressions.md#fields-through-options), [Variant types](04-declarations.md#variant-types)).

## Traits and generics

A trait names methods that several types share, and a type implements it by saying so, with `impl`:

```stilt fragment
trait Label {
  fn label(self) -> str
}

impl Label for Move {
  fn label(self) -> str { "{self.name} ({self.power})" }
}

fn labels<T: Label>(xs: List<T>) -> List<str> { xs.map(|x| x.label()) }
```

TypeScript's types are structural: any object with the right fields fits. Stilt's records are nominal: a `Move` is a `Move` because it was built as one. `==` compares two records field by field, where `===` compares two objects by identity ([Structural impls](06-traits.md#structural-impls)).

## Tasks and parallel loops

`task.spawn` starts a task and gives its handle, and `t.await()` waits for its value, as `await` does for a promise. A `with task.threads() { … }` block runs its tasks on threads and waits for all of them, as `Promise.all` does. `par.map` runs a function over a list on every core.

Waiting is the effect `async`, written in a row as `io` is. A generic function's row passes its callback's effects through, so one `map` takes callbacks that wait, raise or print. In TypeScript, an `async` callback makes `map` give an array of promises ([Effects that pass through](05-errors.md#effects-that-pass-through), [Effects, tasks and parallelism](17-effects.md)).

## Inferred facts and limits

The compiler infers **facts** about every function, such as `alloc` when it allocates, `panic` when it can panic and `overflow` when its arithmetic can overflow. `stilt show` prints them with the operation behind each, and the language server shows them beside each signature ([Ask what the compiler inferred](01-tour.md#ask-what-the-compiler-inferred)). A `without` clause turns facts into a **limit**, which the checker holds the body to. If you index a list in the tour's `fn damage(…) -> i64 without panic, alloc`, it stops compiling ([Limits](05-errors.md#limits)).

## Modules, packages and tests

A file is a module. `use std.fs` imports the whole module, as `import * as fs` does, and code names `fs.read`; there are no named imports and no re-exports. `pub` plays the part of `export`, and a package has no install or build scripts ([Programs](08-programs.md)).

Tests sit beside the code: a `test "name" { … }` block is a test, and a doc comment holds examples, `/// ex:` lines, and properties, `/// prop:` lines. `stilt test` runs a property on generated values, as fast-check does ([Tests](08-programs.md#tests)). [The playground](../../playground/) runs Stilt in the browser.

Arguments are positional: there are no optional parameters, default values or rest parameters ([calls](../../reference/08-expressions.md#expressions.arguments)).
