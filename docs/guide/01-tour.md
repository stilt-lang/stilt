# A tour

In this tour you build a small arena where creatures fight. You start from an empty program and add one thing at a time: a creature, the elements that beat each other, a hit, a whole battle, then tests. Along the way you meet most of the everyday language, and you see what the compiler works out about your code without being told.

It takes about thirty minutes. You need `stilt` on your `PATH`, which [`install.sh`](../../install.sh) sets up; running it again updates to the latest release, and Homebrew and Nix update their own installs. The guide's tests run every program on this page, so each one prints exactly what is shown under it.

## Create the program

Create a program called `arena`, and run it:

```console
$ stilt new arena && cd arena
Created the program `arena` in arena.

Next:
  cd arena
  stilt run
$ stilt run
Hello, arena!
$ stilt test
1 passed, 0 failed
```

`stilt new` makes a directory with a manifest, `stilt.toml`, and one source file, `src/main.lt`:

```stilt
/// The greeting this program prints.
fn greeting(who: str) -> str { "Hello, {who}!" }

fn main() / io {
  print(greeting("arena"))
}

test "greets by name" {
  assert greeting("you") == "Hello, you!"
}
```

```output
Hello, arena!
```

`stilt run` runs `main`. `stilt test` runs each `test` block, and `assert` fails the test when its condition is false. The `/// ` line is a doc comment, and `{who}` inside a string inserts the value of `who`.

The `/ io` after `main()` says that `main` does input and output. Printing is output, so a function that prints must say so. Remove `/ io` and `stilt check` refuses the program:

```stilt E0502:5
/// The greeting this program prints.
fn greeting(who: str) -> str { "Hello, {who}!" }

fn main() {
  print(greeting("arena"))
}
```

```console
$ stilt check
── EFFECT THAT DOESN'T FIT THE ROW ──────────────────── src/main.lt:5:3  [E0502]

This performs `io`, which the row doesn't declare:

  5 │   print(greeting("arena"))
    │   ^^^^^^^^^^^^^^^^^^^^^^^^

A function's row lists the effects it performs, as `/ io` for printing, so that
its callers see them. Add the effect to the row.

To fix it, declare `io` in the signature:

  4 │ fn main() / io {
    │          +++++
```

Every error has a code, here `E0502`, and `stilt show E0502` explains it with examples. Put `/ io` back before you go on.

## Add a creature

A creature has a name, an element, hit points and an attack. Replace `src/main.lt` with this:

```stilt
/// What a creature is made of.
type Element = | Fire | Water | Plant

/// A fighter in the arena.
type Creature = { name: str, element: Element, hp: i64, attack: i64 }

fn main() / io {
  let embercat = Creature { name: "Embercat", element: Fire, hp: 30, attack: 8 }
  print("{embercat}")
  print("{embercat.name} has {embercat.hp} HP.")
}
```

```output
Creature { name: "Embercat", element: Fire, hp: 30, attack: 8 }
Embercat has 30 HP.
```

`Element` is a **variant type**: an element is exactly one of `Fire`, `Water` or `Plant`. `Creature` is a **record**: a value with named fields. `i64` is a 64-bit integer and `str` is text.

`let` names a value. You didn't write the type of `embercat`, because the compiler infers it inside a function. A function's signature is different: its parameter and return types are always written, so you can read what a function takes and gives without reading its body.

You didn't write any code to print a creature either. A record prints itself, field by field, as long as each of its fields can be printed.

## Match the elements

Fire burns plants, water puts out fire, and plants drink water. Write that down as a function:

```stilt
type Element = | Fire | Water | Plant

/// How hard a move of `attacker` lands on `defender`, as a percentage.
fn effectiveness(attacker: Element, defender: Element) -> i64 {
  match (attacker, defender) {
    (Fire, Plant) | (Water, Fire) | (Plant, Water) => 200
    (Fire, Water) | (Water, Plant) | (Plant, Fire) => 50
    _ => 100
  }
}

fn main() / io {
  print("Fire on Plant: {effectiveness(Fire, Plant)}%")
  print("Fire on Water: {effectiveness(Fire, Water)}%")
  print("Fire on Fire: {effectiveness(Fire, Fire)}%")
}
```

```output
Fire on Plant: 200%
Fire on Water: 50%
Fire on Fire: 100%
```

`match` compares a value with each pattern in turn and runs the first arm that fits. Here the value is a pair, so each pattern is a pair too, and `|` joins patterns that share an arm. `_` matches anything. The last expression of a block is its value, so `effectiveness` needs no `return`.

A `match` must handle every possible value. Delete the `_` arm and the compiler names a case you forgot:

```stilt E0329:4
type Element = | Fire | Water | Plant

fn effectiveness(attacker: Element, defender: Element) -> i64 {
  match (attacker, defender) {
    (Fire, Plant) | (Water, Fire) | (Plant, Water) => 200
    (Fire, Water) | (Water, Plant) | (Plant, Fire) => 50
  }
}
```

```console
$ stilt check
── PATTERNS THAT DON'T COVER EVERY VALUE ────────────── src/main.lt:4:3  [E0329]

These patterns don't cover `(Fire, Fire)`:

  4 │   match (attacker, defender) {
    │   ^^^^^^^^^^^^^^^^^^^^^^^^^^^^

A `match` covers every value of its type. Add an arm for each case that the
message names, or a last `_ => …` arm.
```

If you add a fourth element later, every `match` that forgot it will tell you.

## Land a hit

When one creature hits another, the defender loses hit points: the attacker's attack, scaled by the effectiveness of its element. Hit points never go below zero.

```stilt
type Element = | Fire | Water | Plant

type Creature = { name: str, element: Element, hp: i64, attack: i64 }

fn effectiveness(attacker: Element, defender: Element) -> i64 {
  match (attacker, defender) {
    (Fire, Plant) | (Water, Fire) | (Plant, Water) => 200
    (Fire, Water) | (Water, Plant) | (Plant, Fire) => 50
    _ => 100
  }
}

/// `attacker` hits `defender` once, and says what happened.
fn hit(attacker: Creature, inout defender: Creature) -> str {
  let damage = attacker.attack * effectiveness(attacker.element, defender.element) / 100
  defender.hp = (defender.hp - damage).max(0)
  "{attacker.name} hits {defender.name} for {damage}. {defender.name} has {defender.hp} HP left."
}

fn main() / io {
  let embercat = Creature { name: "Embercat", element: Fire, hp: 30, attack: 8 }
  var mossling = Creature { name: "Mossling", element: Plant, hp: 34, attack: 6 }
  print(hit(embercat, inout mossling))
  print("Mossling still has {mossling.hp} HP.")
}
```

```output
Embercat hits Mossling for 16. Mossling has 18 HP left.
Mossling still has 18 HP.
```

A function gets a copy of each argument, so it can't change the caller's values. `hit` needs to change the defender, so its parameter is marked `inout`, and the call marks the argument the same way: `inout mossling`. You can see at the call that `mossling` may change. Only a `var` can change, so `mossling` is a `var`, while `embercat` stays a `let`.

## Run a battle

Now let the two creatures take turns until one of them faints:

```stilt
type Element = | Fire | Water | Plant

type Creature = { name: str, element: Element, hp: i64, attack: i64 }

fn effectiveness(attacker: Element, defender: Element) -> i64 {
  match (attacker, defender) {
    (Fire, Plant) | (Water, Fire) | (Plant, Water) => 200
    (Fire, Water) | (Water, Plant) | (Plant, Fire) => 50
    _ => 100
  }
}

fn hit(attacker: Creature, inout defender: Creature) -> str {
  let damage = attacker.attack * effectiveness(attacker.element, defender.element) / 100
  defender.hp = (defender.hp - damage).max(0)
  "{attacker.name} hits {defender.name} for {damage}. {defender.name} has {defender.hp} HP left."
}

fn main() / io {
  var embercat = Creature { name: "Embercat", element: Fire, hp: 30, attack: 8 }
  var mossling = Creature { name: "Mossling", element: Plant, hp: 34, attack: 6 }
  while embercat.hp > 0 && mossling.hp > 0 {
    print(hit(embercat, inout mossling))
    if mossling.hp > 0 { print(hit(mossling, inout embercat)) }
  }
  let winner = if embercat.hp > 0 { embercat.name } else { mossling.name }
  print("{winner} wins!")
}
```

```output
Embercat hits Mossling for 16. Mossling has 18 HP left.
Mossling hits Embercat for 3. Embercat has 27 HP left.
Embercat hits Mossling for 16. Mossling has 2 HP left.
Mossling hits Embercat for 3. Embercat has 24 HP left.
Embercat hits Mossling for 16. Mossling has 0 HP left.
Embercat wins!
```

`while` repeats its block as long as its condition holds. `if` is an expression, so it gives `winner` a value. Statements end at the end of the line, without semicolons.

Fire beats plants, so Embercat wins in three hits. Give Mossling the `Water` element, and run it again to see the battle turn.

## Ask what the compiler inferred

You never said whether `hit` can fail, or whether it allocates memory. The compiler works it out anyway. Ask it:

```console
$ stilt show main.hit
module main [core]
fn hit(attacker: Creature, inout defender: Creature) -> str [consumes attacker, overflow, alloc] {
  let damage: i64 = attacker.attack * effectiveness(attacker.element, defender.element) / 100 // a `*` can overflow
  defender.hp = (defender.hp - damage).max(0) // a `-` can overflow
  "{attacker.name} hits {defender.name} for {damage}. {defender.name} has {defender.hp} HP left." // consumes `attacker`; an interpolated string allocates; the built-in `show` allocates
}
```

`stilt show` prints the function with the types it inferred, and, in brackets after the signature, its **facts**:

- `overflow`: an integer operation can overflow. A huge attack times 200 doesn't fit in an `i64`, and the program would stop rather than give a wrong number.
- `alloc`: the function allocates memory, here to build the message.
- `consumes attacker`: `hit` uses up its copy of `attacker`, so it can reuse its memory when the caller has no further use for it.

The comment at the end of each line names the operation behind each fact. Editors show the same facts beside your code.

When a function must never do something, say so with `without`, and the compiler holds the function to it. The damage calculation needs no memory, and it can't divide by zero, since it divides by `100`:

```stilt
type Element = | Fire | Water | Plant

type Creature = { name: str, element: Element, hp: i64, attack: i64 }

fn effectiveness(attacker: Element, defender: Element) -> i64 {
  match (attacker, defender) {
    (Fire, Plant) | (Water, Fire) | (Plant, Water) => 200
    (Fire, Water) | (Water, Plant) | (Plant, Fire) => 50
    _ => 100
  }
}

/// The damage one hit of `attacker` does to `defender`.
fn damage(attacker: Creature, defender: Creature) -> i64 without panic, alloc {
  attacker.attack * effectiveness(attacker.element, defender.element) / 100
}
```

`without panic, alloc` is checked, not trusted. Index into a list inside `damage` and the program no longer compiles, because an index out of range would panic. `without panic` still allows an integer to overflow, as `attacker.attack * …` might, and a `deadlock` panic of shared state, which [Shared state](17-effects.md#shared-state) explains: code that must never panic says `without panic, overflow`. A limit covers the code that `damage` names. A function value given to it counts where it was written, and a call of C counts what any C code may do, unless the C function's declaration says less ([Calling C](08-programs.md#calling-c)).

## Refuse a move

A creature that has fainted can't move. That isn't a bug in the program: it's a situation the caller has to handle. Make `hit` **raise** an error:

```stilt exit:1
type Element = | Fire | Water | Plant

type Creature = { name: str, element: Element, hp: i64, attack: i64 }

fn effectiveness(attacker: Element, defender: Element) -> i64 {
  match (attacker, defender) {
    (Fire, Plant) | (Water, Fire) | (Plant, Water) => 200
    (Fire, Water) | (Water, Plant) | (Plant, Fire) => 50
    _ => 100
  }
}

fn hit(attacker: Creature, inout defender: Creature) -> str / raise<str> {
  if attacker.hp == 0 { raise "{attacker.name} has fainted and can't move" }
  let damage = attacker.attack * effectiveness(attacker.element, defender.element) / 100
  defender.hp = (defender.hp - damage).max(0)
  "{attacker.name} hits {defender.name} for {damage}. {defender.name} has {defender.hp} HP left."
}

fn main() / {io, raise<str>} {
  var mossling = Creature { name: "Mossling", element: Plant, hp: 34, attack: 6 }
  let fainted = Creature { name: "Embercat", element: Fire, hp: 0, attack: 8 }
  print(try hit(fainted, inout mossling))
}
```

```stderr
error: Embercat has fainted and can't move
```

`/ raise<str>` says that `hit` can raise an error, and that the error is a `str`. Like `io`, it's part of the signature, so every caller knows.

Each call that can raise is marked with `try`, so you can see every place where a function can stop early. `main` doesn't handle the error here: its signature says it raises a `str` too, so the error goes up, and the program ends with status 1 and prints it. To handle the error instead, add `catch`:

```stilt fragment
let line = try hit(fainted, inout mossling) catch e => "({e})"
```

The compiler knows every error that can reach each line. Forget a `try`, and it tells you where to put one. A raise compiles to a value that the function returns, so a call that doesn't raise costs nothing extra ([how raising is compiled](../../reference/rationale/12-effects.md#raising-and-marking)).

Bugs are different. An index out of range, a division by zero or an overflow **panics**: the program stops at once with status 101, and no `catch` can intercept it.

## Test it

Tests live next to the code they test. Here are three kinds:

```stilt pass:14 fail:15 pass:25
type Element = | Fire | Water | Plant

type Creature = { name: str, element: Element, hp: i64, attack: i64 }

fn effectiveness(attacker: Element, defender: Element) -> i64 {
  match (attacker, defender) {
    (Fire, Plant) | (Water, Fire) | (Plant, Water) => 200
    (Fire, Water) | (Water, Plant) | (Plant, Fire) => 50
    _ => 100
  }
}

/// The hit points left after taking `damage`, never fewer than zero.
/// ex: remaining(10, 4) == 6
/// prop: |hp: i64, damage: i64| remaining(hp, damage) >= 0
fn remaining(hp: i64, damage: i64) -> i64 { (hp - damage).max(0) }

fn hit(attacker: Creature, inout defender: Creature) -> str / raise<str> {
  if attacker.hp == 0 { raise "{attacker.name} has fainted and can't move" }
  let damage = attacker.attack * effectiveness(attacker.element, defender.element) / 100
  defender.hp = remaining(defender.hp, damage)
  "{attacker.name} hits {defender.name} for {damage}. {defender.name} has {defender.hp} HP left."
}

test "a fainted creature can't move" {
  var mossling = Creature { name: "Mossling", element: Plant, hp: 34, attack: 6 }
  let embercat = Creature { name: "Embercat", element: Fire, hp: 0, attack: 8 }
  let message = try hit(embercat, inout mossling) catch e => e
  assert message == "Embercat has fainted and can't move"
}
```

- The `ex:` line is an **example** in the documentation. `stilt test` runs it, so the documentation can't drift from the code.
- The `prop:` line is a **property**: a claim about every input. `stilt test` tries many values of `hp` and `damage`, looking for one that breaks it.
- The `test` block is an ordinary test. `catch e => e` turns the raised error into a value it can compare.

Run the tests:

```console
$ stilt test
src/main.lt:15: property `|hp: i64, damage: i64| remaining(hp, damage) >= 0` failed
  it panicked: overflow: the result is out of range at case 30, with seed 7bf7459771c2ae5b
  counterexample, shrunk once:
    hp = 0
    damage = -9223372036854775808
2 passed, 1 failed
```

The property found a case nobody wrote a test for: with a huge negative `damage`, `hp - damage` overflows. In the arena, damage is never negative, and hit points never are either. Say so in the property, with `||`, so that it only claims what's meant:

```stilt fragment
/// prop: |hp: i64, damage: i64| hp < 0 || damage < 0 || remaining(hp, damage) >= 0
```

```console
$ stilt test
3 passed, 0 failed
```

## Keep going

You now have an arena with two creatures, a battle, an error for fainted creatures, and tests. The guide's chapters go through each part of the language in order:

- [Values and types](02-values.md): numbers, text, lists, maps, and what copying a value means.
- [Declaring types](04-declarations.md): records, variants and `match` in full.
- [Errors and effects](05-errors.md): `raise`, `try`, `catch`, and the `without` limits.
- [Parameter modes](07-modes.md): how `inout` stays safe without references.
- [Programs](08-programs.md): modules, packages and tests.

If you know another language well, [Stilt for Rust programmers](for-rust-programmers.md), and the pages for [Go](for-go-programmers.md), [Python](for-python-programmers.md), [TypeScript](for-typescript-programmers.md) and [Swift](for-swift-programmers.md), map what you know onto Stilt.
