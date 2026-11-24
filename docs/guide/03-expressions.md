# Expressions

A function body is made of expressions. This program rates each move of the arena and prints a table:

```stilt
type Element = | Fire | Water | Plant

type Move = { name: str, element: Element, power: i64 }

fn main() / io {
  let moves = [
    Move { name: "Flame Pounce", element: Fire, power: 40 },
    Move { name: "Root Snare", element: Plant, power: 30 },
    Move { name: "Bubble Jet", element: Water, power: 35 },
  ]
  for m in moves {
    let rating = if m.power >= 35 { "strong" } else { "weak" }
    print("{m.name:<12} {m.power:>3} {rating}")
  }
  let strong = moves.filter(|m| m.power >= 35).map(.name)
  print("Strong: {strong}")
}
```

```output
Flame Pounce  40 strong
Root Snare    30 weak
Bubble Jet    35 strong
Strong: ["Flame Pounce", "Bubble Jet"]
```

The program uses most of this chapter: a `for` loop, an `if` that gives a value, a closure `|m| m.power >= 35`, a key path `.name`, and interpolation with format specs such as `:<12`. Patterns, which `match` and `let` share, are in [Declaring types](04-declarations.md#patterns).

## Comments

A comment starts with `//` and runs to the end of the line. There are no block comments. A comment that starts with `///` is a doc comment, which documents the declaration after it ([Programs](08-programs.md)).

A comment that holds a whole statement is commented-out code, and gets the warning W0001, *commented-out code*:

```stilt W0001:4
fn main() / io {
  // Fire burns plants for double damage.
  let damage = 8 * 2
  // print("debug: {damage}")
  print("{damage}")
}
```

```output
16
```

The comment on line 2 isn't a statement, so it passes, and so does a comment of one word or number, such as `// fallthrough` ([lexical.commented-out-code](../../reference/02-lexical.md#lexical.commented-out-code)). Delete code you no longer use, because a reader takes a comment as true.

## Names and case

An identifier is an ASCII letter or `_`, followed by ASCII letters, digits and `_`. Its case is the case of its first letter, and the case is part of the grammar:

| Case | Names |
| --- | --- |
| Uppercase | Types, type parameters, variants, traits and constants |
| Lowercase | Values, functions, modules, fields, methods and effect-row variables |

So in a pattern, an uppercase name is a constant or a variant to compare with, and a lowercase name binds a new variable:

```stilt
const MAX_HP: i64 = 34

fn describe(hp: i64) -> str {
  match hp {
    MAX_HP => "unhurt"
    left => "{left} HP left"
  }
}

fn main() / io { print("{describe(34)}, {describe(18)}") }
```

```output
unhurt, 18 HP left
```

A declaration whose name has the wrong case, such as `fn Hit()` or `type creature`, is E0100, *syntax error*, and the error offers the right case. A binding can't be uppercase either. `Damage` here is a constant pattern, and no constant `Damage` exists, so the program is E0211, *unknown name*:

```stilt E0211:1
fn main() { let Damage = 8 }
```

`_` alone is the wildcard. A name with no letter at all, such as `__` or `_1`, is E0003, *identifier without a letter*. The primitive type names, such as `i64` and `str`, can't name anything else (E0210, *primitive type name used as a name*).

These words are keywords in core:

| Group | Keywords |
| --- | --- |
| Declarations | `const`, `fn`, `impl`, `module`, `pub`, `test`, `trait`, `type`, `use` |
| Bindings and modes | `inout`, `let`, `var` |
| Control flow | `break`, `continue`, `else`, `for`, `if`, `in`, `loop`, `match`, `return`, `while` |
| Failure | `assert`, `catch`, `raise`, `try` |
| Values and types | `false`, `self`, `Self`, `true` |

These words are reserved as well, in every module: `async`, `await`, `comptime`, `effect`, `extern`, `handler`, `macro`, `quote`, `resume`, `syntax`, `unsafe`, `when`, `where`, `with` and `yield`. A few words, such as `io` and `without`, are keywords only where the grammar expects them, so `use std.io` binds a module named `io` ([lexical.contextual-keywords](../../reference/02-lexical.md#lexical.contextual-keywords)). Words that other languages reserve, such as `as`, `mut` and `ref`, are ordinary names.

## Newlines and terminators

A newline ends a statement, so Stilt needs no semicolons. A line continues onto the next when it ends with an operator or a comma. It also continues when the next line starts with `.`, `else`, `catch` or `|`:

```stilt
fn main() / io {
  let names = ["Embercat", "Mossling", "Tidepup"]
  let loud = names.filter(|n| n.len() > 7).map(|n| n.ascii_upper())
  let total = loud.len() +
    names.len()
  let first = loud.first()
    else "nobody"
  print("{loud} {total} {first}")
}
```

```output
["EMBERCAT", "MOSSLING"] 5 EMBERCAT
```

Inside `(…)` or `[…]`, a newline never ends a statement, so a call or a list can span lines. A block inside them, such as a closure's body, follows the rule again. Newlines never replace commas: a record literal on several lines still needs a comma after each field. [Newlines and terminators](../../reference/02-lexical.md#newlines-and-terminators) gives the exact rule.

`>` and `>>` end a line, because they also close a generic type, as in `List<Option<i64>>`. So a comparison that spans lines goes in parentheses:

```stilt E0100:3
fn main() / io {
  let hp = 30
  let standing = hp >
    0
  print("{standing}")
}
```

A `;` can also separate statements or items, as in `use std.cli; use std.fs`. The formatter never writes one.

## Blocks and statements

A block is a list of statements in braces, and it is an expression too. Its value is its last statement, if that is an expression, and `()` otherwise. A function's body is a block, so its last expression is the result, with no `return`:

```stilt
fn damage(attack: i64, multiplier: i64) -> i64 {
  let raw = attack * multiplier
  raw / 100
}

fn main() / io {
  let message = {
    let d = damage(8, 200)
    "Embercat hits for {d}"
  }
  assert message != ""
  print(message)
}
```

```output
Embercat hits for 16
```

The statements are `let` and `var`, assignments, `assert`, and expressions standing alone. `assert` takes a `bool`, and panics with the kind `assert` when it is false.

An expression that stands alone before the last statement must have type `()` or `Never`. Any other value would be thrown away, which is E0322, *unused value*:

```stilt E0322:3
fn main() / io {
  let hps = [30, 34, 32]
  hps.sorted()
  print("{hps}")
}
```

`sorted` returns a sorted copy and leaves `hps` alone, so this line would do nothing. Write `let hps = hps.sorted()`, or `hps.sort()` on a `var`. To throw a value away on purpose, write `let _ = e`.

## Scope and shadowing

A name is visible from where it is bound to the end of what holds it:

| Binding | Visible in |
| --- | --- |
| A `let` or `var` statement | The rest of its block, from the next statement on |
| A parameter | The whole body of its function or closure |
| The pattern of a `for` | The loop's body |
| The pattern of a `match` or `catch` arm | The arm's guard and body |
| The pattern of an `if let` | Its first block |

A new binding can reuse a visible name, and hides the old binding until its own scope ends. This is called **shadowing**, and it works on functions and prelude items too:

```stilt
fn remaining(hp: i64, damage: i64) -> i64 { (hp - damage).max(0) }

fn main() / io {
  let remaining = remaining(34, 16)
  let hp = remaining
  let hp = hp - 16
  {
    let hp = "fainted?"
    print(hp)
  }
  print("{hp}")
}
```

```output
fainted?
2
```

A `let` takes effect at the next statement, so the right side of `let remaining = remaining(34, 16)` still sees the function, and `let hp = hp - 16` reads the earlier `hp`. The inner `hp` ends with its block.

Shadowing is how you make a value changeable, as in `var hp = hp`. A local can't take the name of a module that `use` imports, which is E0207, *local named after an imported module* ([Programs](08-programs.md)).

## `if`

`if` is an expression. Its condition is a `bool` with no parentheses, and its branches are blocks. An `else` is followed by a block or by another `if`:

```stilt
fn main() / io {
  for multiplier in [200, 100, 50] {
    let verdict = if multiplier > 100 { "super effective" } else if multiplier < 100 { "weak" } else { "normal" }
    print("{multiplier}: {verdict}")
  }
}
```

```output
200: super effective
100: normal
50: weak
```

With an `else`, both branches must have the same type. A branch of type `Never`, such as a `return`, fits any type. Without an `else`, the `if` has type `()`, and its block must have type `()` or `Never`. Any other value would be lost, which is E0323, *value of an `if` without `else`*:

```stilt E0323:2
fn remaining(hp: i64, damage: i64) -> i64 {
  if damage > hp { 0 }
  hp - damage
}
```

To return early, write `if damage > hp { return 0 }`.

The condition ends at the first `{` outside parentheses and brackets, which always opens the body. So `if hp == MAX_HP {` means what it says. A struct literal, a block or another `if` in a condition needs parentheses, as in `if c == (Point { x: 0, y: 0 }) {` ([expressions.heads](../../reference/08-expressions.md#expressions.heads)). The same rule holds for `while`, `match` and the list of a `for`.

## `match`

`match` compares a value with each pattern in turn and takes the first arm that matches. An arm can have a guard, `if c`, which must also hold. Arms are separated by newlines or commas:

```stilt
fn status(hp: i64) -> str {
  match hp {
    0 => "fainted"
    1 | 2 => "barely standing"
    h if h < 10 => "hurt"
    _ => "fine"
  }
}

fn main() / io { print("{status(0)}, {status(2)}, {status(7)}, {status(30)}") }
```

```output
fainted, barely standing, hurt, fine
```

As with `if`, the arms must have the same type. The arms must also cover every value. [Declaring types](04-declarations.md#patterns) covers the patterns and that check.

## `if let`

`if let P = e { … }` runs its block when the value of `e` matches the pattern `P`. The names that `P` binds are visible only in that block. An `else` runs when the value doesn't match:

```stilt
fn main() / io {
  let hps = [30, 34, 32]
  if let [first, ..] = hps { print("first {first}") }
  if let Some(hp) = hps.get(5) { print("{hp}") } else { print("no sixth creature") }
}
```

```output
first 30
no sixth creature
```

Use `if let` where a `match` would have one arm that matters and a `_` arm that does nothing. It types as `if` does, and `else if let` chains like `else if`. There is no `while let`: inside a `loop`, write `let P = e else break` ([Declaring types](04-declarations.md#let-and-let-else)). [expressions.if-let-matching](../../reference/08-expressions.md#expressions.if-let-matching) gives how an `else` in `e` itself is read.

## Loops

Stilt has three loops: `for p in e { … }`, `while c { … }` and `loop { … }`. A `for` goes through a list, a map in insertion order, or a range of integers. `a..b` runs from `a` up to `b`, without `b`, and `a..=b` includes `b`:

```stilt
fn main() / io {
  var hp: Map<str, i64> = Map.new()
  hp["Embercat"] = 30
  hp["Mossling"] = 34
  for (name, points) in hp { print("{name}: {points}") }
  var total = 0
  for round in 1..=3 { total += round }
  for i in 0..2 { print("round {i}") }
  print("{total}")
}
```

```output
Embercat: 30
Mossling: 34
round 0
round 1
6
```

A map gives `(key, value)` pairs, which the pattern `(name, points)` takes apart. The pattern of a `for` must match every value, as a `let` pattern must. A range of floats, such as `0.0..1.5`, is E0317, *operator not defined on a type* ([expressions.for-iterables](../../reference/08-expressions.md#expressions.for-iterables)).

A range isn't a value: `a..b` can appear only after `for … in`, and `let r = 0..10` is E0100, *syntax error*. `..` binds more loosely than every operator, so `for i in 0..n + 1` runs to `n`.

`break` leaves the innermost loop, and `continue` starts its next turn. Neither takes a label or a value:

```stilt
fn main() / io {
  var hp = 34
  var round = 0
  loop {
    round += 1
    if round % 2 == 0 { continue }
    hp -= 16
    if hp <= 0 { break }
    print("round {round}: {hp} HP")
  }
  print("fainted in round {round}")
}
```

```output
round 1: 18 HP
round 3: 2 HP
fainted in round 5
```

`while` and `for` have type `()`. A `loop` with a `break` has type `()` too, and a `loop` without one has type `Never`. So a `loop` that leaves only through `return` can end a function of any return type:

```stilt
fn hits_to_faint(hp: i64, damage: i64) -> i64 {
  var hits = 1
  loop {
    if hits * damage >= hp { return hits }
    hits += 1
  }
}

fn main() / io { print("{hits_to_faint(34, 16)}") }
```

```output
3
```

A `break` or `continue` outside a loop's body is E0216, *`break` or `continue` outside a loop*. A closure's body counts as outside, even when the closure is written inside a loop:

```stilt E0216:3
fn main() / io {
  for name in ["Embercat", "", "Tidepup"] {
    let skip = |s: str| if s.is_empty() { continue }
    skip(name)
    print(name)
  }
}
```

Changing a list while a `for` loop goes through it is E0404, which [Parameter modes](07-modes.md) explains.

## Operators and precedence

Operators bind as this table says, from tightest to loosest:

| Level | Forms | Associativity |
| --- | --- | --- |
| 1 | Literals, names, `(…)`, tuples, `[…]`, struct literals, blocks, `if`, `match`, loops, closures, key paths, holes `?` | |
| 2 | Calls `f(x)`, fields `.x` and `.0`, method calls `.m(x)` and indexing `[i]` | left |
| 3 | Prefix `-` and `!` | right |
| 4 | `*` `/` `%` `*%` | left |
| 5 | `+` `-` `+%` `-%` | left |
| 6 | `<<` `>>` | left |
| 7 | `&` | left |
| 8 | `^` | left |
| 9 | `\|` | left |
| 10 | `==` `!=` `<` `<=` `>` `>=` | none |
| 11 | `&&` | left |
| 12 | `\|\|` | left |
| 13 | `else`, the `Option` fallback | right |
| 14 | `try`, `try … catch`, `raise`, `return`, `break`, `continue`, closure bodies | prefix |

Unlike in C, the bitwise operators bind more tightly than the comparisons, so `hp & 1 == 0` tests whether `hp` is even. Unlike in Go, the shifts bind more loosely than `+`:

```stilt
fn main() / io {
  let hp = 6
  print("{1 + 2 << 1} {hp & 1 == 0} {-hp / 4} {hp > 2 && hp < 10 || hp == 0}")
}
```

```output
6 true -1 true
```

The operand of `try`, `raise` or `return`, and a closure's body, reach as far right as they can. A `catch` belongs to the innermost `try` still open where it appears ([expressions.catch-attachment](../../reference/08-expressions.md#expressions.catch-attachment)).

Every binary operator evaluates its left operand first. `&&` and `||` evaluate the right one only when they need it ([Booleans](02-values.md#booleans)).

Comparisons don't chain. `a < b < c` is E0100, *syntax error*, so write `a < b && b < c`:

```stilt E0100:1
fn in_range(low: i64, hp: i64, high: i64) -> bool { low <= hp <= high }
```

Both operands of an arithmetic operator or a comparison have the same type. A mismatch is E0311, *mismatched types*, at the right operand:

```stilt E0311:1
fn boosted(attack: i64) -> i64 { attack * 1.5 }
```

If the operator isn't defined on the left operand's type at all, the error is E0317, *operator not defined on a type*. The right operand doesn't matter. `+` isn't defined on `str`, so the error offers interpolation as the fix:

```stilt E0317:1
fn label(hp: i64) -> str { "HP: " + hp }
```

The fix is `"HP: {hp}"`. On types other than numbers, `==` and `<` use the `Eq` and `Ord` traits ([Traits and generics](06-traits.md)). [Values and types](02-values.md#integer-arithmetic) covers what each operator does on numbers.

Every list separated by commas can end with a comma: arguments, parameters, elements, fields and patterns.

## Type inference

The compiler infers types inside each body: a function's body, a test, a doc example or a constant's value. A body's types depend on the signatures it uses, never on another body ([types.inferred-per-body](../../reference/07-types.md#types.inferred-per-body)).

The compiler checks a body in the order it runs. Each expression is checked against the type its context expects, if any: an annotation, a parameter's type, a return type, a field's type, or the type an earlier element or branch set. A literal takes its type from the whole body, so the `0` of `total` here is an `f64`:

```stilt
fn main() / io {
  var multipliers: Map<str, f64> = Map.new()
  multipliers["Fire on Plant"] = 2.0
  multipliers["Fire on Water"] = 0.5
  var total = 0
  for (_, m) in multipliers { total += m }
  var seen = []
  seen.push(total)
  print("{total} {seen}")
}
```

```output
2.5 [2.5]
```

Some types must be known where they are used, from what comes before: the receiver of a method call, the value whose field is read, an indexed value and the list of a `for`. Knowing the outer type is enough. `seen` is known to be a `List` from `[]` on, so `seen.push(total)` is valid, and the call decides what the list holds. Any other unknown type there is E0312, *type that can't be inferred*, as is a type that the whole body leaves open ([types.undecided-types](../../reference/07-types.md#types.undecided-types)).

Expressions never take type arguments, so `<` in an expression always means less-than. There is no `Map.new<str, f64>()`: write the annotation `var multipliers: Map<str, f64>` instead.

## Assignment

Assignment is a statement, `place = e` or `place op= e`. A **place** is a variable followed by any number of fields `.f`, tuple elements `.0` and indexes `[i]`:

```stilt
type Element = | Fire | Water | Plant

type Creature = { name: str, element: Element, hp: i64, attack: i64 }

fn main() / io {
  var embercat = Creature { name: "Embercat", element: Fire, hp: 30, attack: 8 }
  embercat.hp -= 3
  var team = [(embercat, 0), (embercat, 0)]
  team[1].0.attack *= 2
  team[1].1 += 1
  print("{embercat.hp} {team[1].0.attack} {team[1].1}")
}
```

```output
27 16 1
```

Each binary arithmetic, wrapping and bitwise operator has a compound form, such as `+=`, `+%=` and `<<=`. A place must start at a `var` or an `inout` parameter. Assigning to a `let` binding, or to any part of one, is E0403, *modifying what can't be modified*:

```stilt E0403:3
fn main() / io {
  let hp = 30
  hp -= 8
  print("{hp}")
}
```

To change a value bound with `let`, bind it again first: `var hp = hp`.

`place = e` evaluates the indexes in the place, then `e`, then stores ([values.assignment-order](../../reference/05-values.md#values.assignment-order)). Assignment has no value, so `if hp = 0` can't be written by mistake.

## String interpolation

Every string literal interpolates: `{expr}` inside a string is replaced by the text of the value of `expr`. Any expression can go there, calls and other strings included. A string shows as its text on its own, and in quotes inside another value, such as a list:

```stilt
fn main() / io {
  let name = "Embercat"
  let moves = ["Flame Pounce", "Bubble Jet"]
  print("{name} knows {moves.len()} moves: {moves}")
  print("\{name} is not interpolated, and \"quotes\" are escaped: \u{2603}")
}
```

```output
Embercat knows 2 moves: ["Flame Pounce", "Bubble Jet"]
{name} is not interpolated, and "quotes" are escaped: ☃
```

The value's type must implement `Show`, or the program is E0318, *unsatisfied bound* ([Traits and generics](06-traits.md)). Records, variants, lists, maps and tuples of shown values all print themselves.

The escapes are `\n`, `\t`, `\r`, `\0`, `\\`, `\"`, `\{` and `\u{…}`, which takes 1 to 6 hex digits. Any other escape is E0006, *invalid escape*, and so is `{{`. Only `{` needs an escape, because a lone `}` is an ordinary character. A string can't hold a raw newline, so use `\n`.

### Format specs

An interpolation can carry a format spec after a colon, `{expr:spec}`. A spec has the form `[[fill]align][width][.precision][kind]`, and each part is optional:

| Part | Values | Meaning |
| --- | --- | --- |
| `fill` | Any one character but `{` and `}` | Pads the text, with a space by default |
| `align` | `<`, `^` or `>` | Left, centre or right. Numbers align right by default, everything else left |
| `width` | A number | The width to pad to, in Unicode scalar values |
| `precision` | `.` and a number | For floats, exactly this many digits after the point |
| `kind` | `x`, `X`, `o`, `b` or `e` | For integers, hexadecimal, uppercase hexadecimal, octal or binary. For floats, scientific notation |

The arena's numbers, formatted:

```stilt
fn main() / io {
  let name = "Tidepup"
  let hp = 32
  let small: i8 = -1
  let multiplier = 1.456
  print("[{name:<9}] [{name:>9}] [{name:*^10}]")
  print("[{hp:5}] [{hp:0>5}] [{hp:x}] [{hp:b}] [{small:X}]")
  print("[{multiplier:.2}] [{multiplier:8.1}] [{multiplier:.0}] [{multiplier:e}]")
}
```

```output
[Tidepup  ] [  Tidepup] [*Tidepup**]
[   32] [00032] [20] [100000] [FF]
[1.46] [     1.5] [1] [1.456e0]
```

When the padding is odd, centred text puts the extra fill on the right. Pad with zeros as with any fill, `{hp:0>5}`: a width that starts with `0`, as in `{hp:05}`, is E0007, *malformed format spec*. A negative integer under `x`, `X`, `o` or `b` prints its two's complement, so the `i8` value `-1` prints as `FF`. [Showing and formatting](../../reference/17-std.md#showing-and-formatting) gives the exact output of each spec.

A spec that doesn't fit the value's type is E0325, *invalid format spec*. A precision and `e` apply only to floats, and `x`, `X`, `o` and `b` only to integers. A spec never decides the type of a literal, so here `hp` is an `i64`, and `.2` doesn't apply:

```stilt E0325:3
fn main() / io {
  let hp = 30
  print("{hp:.2}")
}
```

## Closures

A **closure** is a function written inside an expression: `|p₁, …, pₙ| body`, or `|| body` with no parameters. Its body is one expression, or a block for several statements. A parameter's type comes from the function type the context expects, from an annotation such as `|hp: i64|`, or from how the body uses it. The return type is always inferred:

```stilt
fn twice(f: fn(i64) -> i64, hp: i64) -> i64 { f(f(hp)) }

fn main() / io {
  var damage = 8
  let hit = |hp| hp - damage
  damage = 100
  let pairs = [("Embercat", 30), ("Mossling", 34)]
  let labels = pairs.map(|(name, hp)| "{name}={hp}")
  print("{twice(hit, 30)} {hit(34)} {damage} {labels}")
}
```

```output
14 26 100 ["Embercat=30", "Mossling=34"]
```

A closure captures the variables it uses by copy, when it is created. `hit` captured `damage` while it was 8, and the later assignment doesn't reach it. The parameters are patterns, so `|(name, hp)|` takes each pair apart.

A closure can't change a variable it captures: not by assignment, not as an `inout` argument, and not with a method such as `push`. Any of these is E0403, *modifying what can't be modified*:

```stilt E0403:3
fn main() / io {
  var hits = 0
  let count = || { hits += 1 }
  count()
  print("{hits}")
}
```

A method call needs its receiver's type first ([Type inference](#type-inference)). So a method call on a parameter with no annotation and no expected type is E0312, *type that can't be inferred*:

```stilt E0312:2
fn main() / io {
  let shout = |name| name.ascii_upper()
  print(shout("Tidepup"))
}
```

`|name: str| name.ascii_upper()` fixes it.

A closure's parameter can be marked `inout`, as in `|inout c|`. The closure then changes the caller's place through that parameter, as a function does, and a call marks the argument `inout`:

```stilt
type Element = | Fire | Water | Plant

type Creature = { name: str, element: Element, hp: i64, attack: i64 }

fn main() / io {
  var tidepup = Creature { name: "Tidepup", element: Water, hp: 32, attack: 7 }
  let changes: List<fn(inout Creature)> = [|inout c| { c.hp -= 5 }, |inout c| { c.attack += 2 }]
  for change in changes { change(inout tidepup) }
  print("{tidepup.hp} {tidepup.attack}")
}
```

```output
27 9
```

An `inout` parameter is a name, not a pattern. The closure still can't change what it captures ([expressions.inout-closure-parameters](../../reference/08-expressions.md#expressions.inout-closure-parameters)).

A few more rules apply to closures:

- A closure bound by `let` has one type. After `let same = |x| x`, the call `same(1)` makes it take an `i64`, and `same("s")` is E0311, *mismatched types*. A function that works on several types is a generic `fn` ([Traits and generics](06-traits.md)).
- `return` in a closure returns from the closure. `break` and `continue` can't leave it, as [Loops](#loops) shows.
- A closure can't call itself. Declare a recursive function with `fn`.
- At the start of an operand, `|` or `||` begins a closure. After an operand, `|` is bitwise or and `||` is logical or. In a pattern, `|` separates alternatives.

## Key paths

A **key path** is a short closure that reads part of its argument: `.name` means `|x| x.name`. The chain after the `.` can hold fields, tuple elements, method calls and indexes, as in `.1`, `.name.len()` or `.moves[0]`:

```stilt
type Element = | Fire | Water | Plant

type Move = { name: str, element: Element, power: i64 }

fn main() / io {
  let moves = [
    Move { name: "Flame Pounce", element: Fire, power: 40 },
    Move { name: "Root Snare", element: Plant, power: 30 },
    Move { name: "Bubble Jet", element: Water, power: 35 },
  ]
  print("{moves.map(.name)} {moves.map(.name.len())}")
  print("{moves.sorted_by(.power).map(.name)}")
  let pairs = [("Embercat", 30), ("Mossling", 34)]
  print("{pairs.map(.1)}")
}
```

```output
["Flame Pounce", "Root Snare", "Bubble Jet"] [12, 10, 10]
["Root Snare", "Bubble Jet", "Flame Pounce"]
[30, 34]
```

A key path can stand only where a function type is expected. Anywhere else it is E0324, *key path where no function is expected*. An annotation gives it one: `let power: fn(Move) -> i64 = .power` is valid.

```stilt E0324:3
type Move = { name: str, power: i64 }

fn main() { let get = .power }
```

## The `else` fallback

`e₁ else e₂` takes the value out of an `Option`. If `e₁` is a `Some`, the result is its value. If `e₁` is `None`, the result is `e₂`, which runs only then. `e₂` has the type inside the `Option`, or `Never`, so it can also leave early:

```stilt
fn parse_hp(text: str) -> i64 { text.to_i64() else 30 }

fn strongest(powers: List<i64>) -> i64 {
  let first = powers.first() else return 0
  powers.fold(first, |a, b| a.max(b))
}

fn main() / io {
  let chosen: Option<str> = None
  let backup: Option<str> = Some("Tidepup")
  print("{parse_hp("34")} {parse_hp("lots")}")
  print("{strongest([40, 30, 35])} {strongest([])}")
  print(chosen else backup else "Embercat")
}
```

```output
34 30
40 0
Tidepup
```

`else` binds more loosely than every binary operator and groups to the right. So `chosen else backup else "Embercat"` means `chosen else (backup else "Embercat")`, and tries each option in turn.

The fallback works only on `Option`. Convert a `Result` with `.ok()` first. `else` on a `Result` is E0311, *mismatched types*:

```stilt E0311:1
fn hp_or_zero(r: Result<i64, str>) -> i64 { r else 0 }
```

An `else` right after the block of an `if` belongs to the `if`. After a pattern that can fail, as in `let Some(m) = moves.first() else return`, it makes a let-else ([Declaring types](04-declarations.md#let-and-let-else)). Everywhere else it is the fallback. [Errors and effects](05-errors.md) shows how `Option`, `Result` and `raise` fit together.

## Fields through options

A field read on an `Option` reads the field of the value inside it. The result is `None` if the `Option` is `None`, and the field's value in a `Some` otherwise:

```stilt
type Element = | Fire | Water | Plant

type Creature = { name: str, element: Element, hp: i64, attack: i64 }

type Trainer = { name: str, partner: Option<Creature>, title: Option<str> }

fn main() / io {
  let embercat = Creature { name: "Embercat", element: Fire, hp: 30, attack: 8 }
  let ana = Trainer { name: "Ana", partner: Some(embercat), title: Some("Champion") }
  let bo = Trainer { name: "Bo", partner: None, title: None }
  print("{ana.partner.hp} {bo.partner.hp}")
  print("{ana.title} {bo.title}")
  for winner in [Some(ana), Some(bo), None] { print(winner.partner.name else "no one") }
}
```

```output
Some(30) None
Some("Champion") None
Embercat
no one
no one
```

A read through an `Option` adds no second level of `Option`. `title` is an `Option<str>` already, so `ana.title` is too. A whole path holds one `Option`, however many of its links are optional. `winner.partner.name` is an `Option<str>`, which is `None` when there is no winner or the winner has no partner. The field's type decides, so it must be known at the read ([types.option-field-known](../../reference/07-types.md#types.option-field-known)).

Nothing in the code marks a link as optional: the type does. Where a value of the type inside is expected, a path through an `Option` is E0311, *mismatched types*, and `else` gives it a fallback:

```stilt E0311:7
type Element = | Fire | Water | Plant

type Creature = { name: str, element: Element, hp: i64, attack: i64 }

type Trainer = { name: str, partner: Option<Creature> }

fn partner_name(t: Trainer) -> str { t.partner.name }
```

The fix is `t.partner.name else "no one"`.

Only fields read through an `Option`. A method called on an `Option` is a method of `Option`, such as `map` and `filter`. To call a method of the value inside, use `map`, or give a fallback first, as in `(t.title else "").len()`. Key paths read through options as fields do:

```stilt
type Trainer = { name: str, title: Option<str> }

fn main() / io {
  let trainers = [Trainer { name: "Ana", title: Some("Champion") }, Trainer { name: "Bo", title: None }]
  print("{trainers.map(.title.map(.len()))} {trainers.filter_map(.title)}")
  print("{trainers.first().title} {(trainers[1].title else "").len()}")
}
```

```output
[Some(8), None] ["Champion"]
Some("Champion") 0
```

`filter_map` keeps the values inside each `Some` ([Option, Result and Ordering](09-library.md#option-result-and-ordering)).

A field that the type inside lacks is E0313, *no such field*. A `Result` has no fields at all, so convert it with `.ok()` first:

```stilt E0313:5
type Element = | Fire | Water | Plant

type Creature = { name: str, element: Element, hp: i64, attack: i64 }

fn name(r: Result<Creature, str>) -> Option<str> { r.name }
```

A field read through an `Option` is a copy, not a place, so changing it would change nothing. Assigning to one, passing one `inout` or calling a method that changes it is E0401, *not a place*:

```stilt E0401:7
type Element = | Fire | Water | Plant

type Creature = { name: str, element: Element, hp: i64, attack: i64 }

fn main() {
  var partner: Option<Creature> = Some(Creature { name: "Embercat", element: Fire, hp: 30, attack: 8 })
  partner.hp = 0
}
```
