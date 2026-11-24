# Values and types

Every value in this program has a built-in type:

```stilt
fn main() / io {
  let name = "Embercat"
  let hp = 30
  let multiplier = 1.5
  let fainted = false
  let stats = (hp, 8)
  let moves = ["Flame Pounce", "Bubble Jet"]
  var wins: Map<str, i64> = Map.new()
  wins[name] = 3
  print("{name} {hp} {multiplier} {fainted} {stats} {moves} {wins}")
}
```

```output
Embercat 30 1.5 false (30, 8) ["Flame Pounce", "Bubble Jet"] {"Embercat": 3}
```

`name` is a `str`, `hp` an `i64`, `multiplier` an `f64` and `fainted` a `bool`. `stats` is a tuple, `moves` a `List<str>` and `wins` a `Map<str, i64>`. Every one of them prints through interpolation, `"{…}"`. A string prints as it is on its own, and in quotes inside another value, as in `moves`.

These are the built-in types:

| Type | Its values | Written as |
| --- | --- | --- |
| `bool` | `true` and `false` | `true` |
| `i8`, `i16`, `i32`, `i64` | Signed integers | `42`, `-7`, `0xff` |
| `u8`, `u16`, `u32`, `u64` | Unsigned integers | `200` |
| `f32`, `f64` | IEEE 754 floats | `2.5`, `1e-3` |
| `str` | Text, as UTF-8 bytes | `"Embercat"` |
| `()` | The single value `()` | `()` |
| `Never` | No values | |
| `(A, B, …)` | Tuples | `(30, "Embercat")` |
| `List<T>` | Lists of `T` | `[30, 34, 32]` |
| `Map<K, V>` | Maps from `K` to `V` | `Map.new()` |

Every module can name them without an import, because they are in the [prelude](../../reference/04-programs.md#program.contents). So are `Option`, `Result` and `Ordering`, which are ordinary variant types ([Declaring types](04-declarations.md)). Function types, such as `fn(i64) -> bool`, come with closures in [Expressions](03-expressions.md#closures).

## Numbers

Stilt has eight integer types and two float types. A signed type of n bits, such as `i8`, holds −2ⁿ⁻¹ to 2ⁿ⁻¹ − 1. An unsigned one, such as `u8`, holds 0 to 2ⁿ − 1. `f32` and `f64` are IEEE 754 binary32 and binary64. `bool` isn't a numeric type.

Each integer type has the constants `MIN` and `MAX`, and each float type has `PI`, `E`, `NAN` and `INFINITY`:

```stilt
fn main() / io {
  let moves = ["Flame Pounce", "Root Snare"]
  let missing = moves.len() - 3
  print("{i8.MIN} {u8.MAX} {i64.MAX} {missing}")
}
```

```output
-128 255 9223372036854775807 -1
```

Lengths, indices and counts are `i64`, and there is no `usize` ([numbers.lengths-are-i64](../../reference/06-numbers.md#numbers.lengths-are-i64)). So `moves.len() - 3` is `-1` rather than an overflow, and a length mixes with other integers without a conversion.

## Number literals

An integer literal is decimal, or hexadecimal, octal or binary after `0x`, `0o` or `0b`. A `_` can separate two digits. A float literal has a fraction, an exponent or both:

```stilt
fn main() / io {
  let million = 1_000_000
  let mask = 0xff
  let mode = 0o755
  let flags = 0b1010
  let ratio = 2.5e-3
  print("{million} {mask} {mode} {flags} {ratio}")
}
```

```output
1000000 255 493 10 0.0025
```

A decimal literal with a leading zero, such as `007`, is E0004, *malformed number literal*. So is a type suffix, as in `10u8`, and a `_` that isn't between two digits. `1.` and `.5` aren't float literals. [Literals](../../reference/02-lexical.md#lexical.integer-literals) gives every form.

## The type of a literal

A literal has no type of its own. It takes the type its context expects, such as an annotation, a parameter's type or the type of the other operand. An integer literal can become any numeric type, a float type included. A float literal can become only a float type:

```stilt
fn scaled(power: f64, multiplier: f64) -> f64 { power * multiplier }

fn main() / io {
  let hp: u8 = 200
  let base: f64 = 1
  print("{hp} {base} {scaled(40, 2)}")
}
```

```output
200 1.0 80.0
```

A literal that doesn't fit its type is E0320, *literal out of range*. As a float, an integer literal fits only when the float type holds it exactly. A float literal fits when it rounds to a finite value:

```stilt E0320:2 E0320:3 E0320:4
fn main() {
  let hp: u8 = 256
  let exact: f64 = 9007199254740993
  let huge: f32 = 1e39
}
```

2⁵³ + 1 is the first integer that `f64` can't hold, so line 3 is an error instead of a silent rounding. A float literal where an integer is expected, as in `let hp: i64 = 30.0`, is E0311, *mismatched types*.

A `-` written right before a literal counts as part of it, so `-128` is a valid `i8`. A `-` before anything else negates a value, and `128` doesn't fit in an `i8` before it is negated ([numbers.negative-literals](../../reference/06-numbers.md#numbers.negative-literals)):

```stilt E0320:3
fn main() {
  let low: i8 = -128
  let wrong: i8 = -(128)
}
```

### Default types

If nothing in a body decides the type of a literal, it becomes `i64`, or `f64` for a float literal. The compiler looks at the whole body first, so a later line can decide the type of an earlier literal:

```stilt
fn total(multipliers: List<f64>) -> f64 {
  var sum = 0
  for m in multipliers { sum += m }
  sum
}

fn main() / io {
  let big = 3000000000
  print("{total([1.5, 2.5])} {big}")
}
```

```output
4.0 3000000000
```

`sum += m` makes `sum` an `f64`, although it starts as the literal `0`. Nothing decides `big`, so it is an `i64`.

A method call is the exception. Which method runs depends on the receiver's type, so a literal whose type is still open there takes its default type on the spot ([numbers.literal-defaults](../../reference/06-numbers.md#numbers.literal-defaults)):

```stilt E0311:4
fn boosted(attack: i32) -> i32 {
  let bonus = 3
  let shown = bonus.abs()
  attack * bonus
}
```

Without line 3, `bonus` would be an `i32`. With it, `bonus` is an `i64` from `bonus.abs()` on, so `attack * bonus` mixes two types.

## Integer arithmetic

The operands of an arithmetic operator or a comparison must have the same type. Nothing converts on its own, not even `i32` to `i64`. If `n` is an `i64` and `multiplier` an `f64`, `n * multiplier` is E0311, *mismatched types*, and the error offers `n.to_f64() * multiplier` as the fix.

`+`, `-` and `*` panic with the kind `overflow` when the result is out of range, in every build ([numbers.integer-panics](../../reference/06-numbers.md#numbers.integer-panics)). For arithmetic that wraps in two's complement, use `+%`, `-%` and `*%`, or their compound forms such as `+%=`:

```stilt exit:101
fn main() / io {
  let hp: u8 = 250
  print("{hp +% 10}")
  print("{hp + 10}")
}
```

```output
4
```

The second `print` never runs. `hp + 10` panics, and the program exits with status 101 ([Errors and effects](05-errors.md)).

`/` truncates toward zero, and the result of `%` has the sign of the dividend. Dividing an integer by zero panics with the kind `divide-by-zero`:

```stilt
fn main() / io { print("{7 / 2} {-7 / 2} {7 % -2} {-7 % 2}") }
```

```output
3 -3 1 -1
```

On integers, `&`, `|`, `^` and `!` work bit by bit. `<<` and `>>` shift the left operand, and the result has its type. The amount can have any integer type. A negative amount, or one at least the width of the type, panics with the kind `overflow`. [Arithmetic](../../reference/06-numbers.md#arithmetic) gives the rest, such as which operators floats lack.

## Conversions

A conversion is a method named after its target type, `.to_T()`. If the conversion can fail, it returns an `Option<T>`:

| Conversion | Result |
| --- | --- |
| Integer to an integer type that holds every value of the source | `T` |
| Integer to an integer type that doesn't | `Option<T>`, `None` when the value doesn't fit |
| Integer to float | `T`, rounded to nearest |
| Float to integer | `Option<T>`, truncated toward zero, `None` for NaN, an infinity or a value out of range |
| Float to float | `T`, rounded to nearest |

For each integer type, `.wrap_to_T()` keeps the low bits instead. A `str` has a `.to_T()` for each numeric type, which parses the whole string:

```stilt
fn main() / io {
  let hp: u8 = 200
  let wide = hp.to_i64()
  let big = 300
  let multiplier = 2.99
  print("{wide} {wide.to_u8()} {big.to_u8()} {big.wrap_to_u8()}")
  print("{multiplier.to_i64()} {wide.to_f64()} {"30".to_i64()} {"3x".to_i64()}")
}
```

```output
200 Some(200) None 44
Some(2) 200.0 Some(30) None
```

`u8` to `i64` can't fail, so `wide` is an `i64`. `i64` to `u8` can, so `wide.to_u8()` is an `Option<u8>`. A parse takes decimal digits, with a leading `-` for a signed type or a float, and a fraction and an exponent for a float. It rejects everything else, such as `+`, spaces and `_` ([numbers.parsing](../../reference/06-numbers.md#numbers.parsing)).

## Floats

Float operations follow IEEE 754 and never panic. Dividing by zero gives an infinity or NaN, and NaN is unequal to everything, itself included. `%` on floats truncates, as C's `fmod` does:

```stilt
fn main() / io {
  let zero = 0.0
  let nan = zero / zero
  print("{1.0 / zero} {-1.0 / zero} {nan} {nan == nan} {7.5 % 2.0}")
  let single: f32 = 0.1
  let double = 0.1
  print("{single * 3.0} {double * 3.0}")
}
```

```output
inf -inf nan false 1.5
0.3 0.30000000000000004
```

Each `f32` operation rounds its result to `f32`. Sorting uses `compare`, a total order in which NaN is greater than every other value ([Traits and generics](06-traits.md)). Floats don't implement `Hash`, so a float can't be a map key.

The core library has only the float operations that IEEE 754 defines exactly, such as `sqrt`, `floor` and `round` ([std.floats](../../reference/17-std.md#std.floats)). So every implementation computes the same bits.

## Printed numbers

An integer prints in decimal. A float prints the shortest digits that read back as the same value, so `0.1` prints as `0.1`, and `0.1 + 0.2` as `0.30000000000000004`. An `f32` prints the shortest digits that read back as the same `f32`, which is why `single * 3.0` above prints `0.3`.

A float whose magnitude is at least `0.0001` and below `1e16` prints in fixed notation, with at least one digit after the point. Any other float prints in scientific notation:

| Value | Prints as |
| --- | --- |
| `1.0` | `1.0` |
| `0.0001` | `0.0001` |
| `0.00001` | `1e-5` |
| `1e15` | `1000000000000000.0` |
| `1e16` | `1e16` |
| NaN, the infinities | `nan`, `inf`, `-inf` |

The compiler and the reference interpreter print the same digits ([Printing](../../reference/06-numbers.md#printing)). To print a fixed number of decimals, use a format spec, as in `"{multiplier:.2}"` ([Format specs](03-expressions.md#format-specs)).

## Booleans

`bool` has the values `true` and `false`. The logical operators are `&&`, `||` and `!`, and exclusive or is `!=`. `&&` and `||` evaluate their right operand only when the left one doesn't decide the result, so the left operand can guard the right one:

```stilt
fn first_is_embercat(names: List<str>) -> bool { names.len() > 0 && names[0] == "Embercat" }

fn main() / io {
  let hp = 0
  let fainted = hp == 0
  print("{fainted} {!fainted} {fainted != true} {first_is_embercat([])}")
}
```

```output
true false false false
```

`names[0]` would panic on an empty list, but `&&` never evaluates it.

No other type stands in for a `bool`. Conditions, guards, the operand of `assert` and the operands of `&&` and `||` must be a `bool`. Anything else there is E0311, *mismatched types* ([expressions.conditions](../../reference/08-expressions.md#expressions.conditions)):

```stilt E0311:1
fn status(hp: i64) -> str { if hp { "standing" } else { "fainted" } }
```

Write the condition out instead: `if hp > 0`.

## Strings

A `str` is an immutable sequence of UTF-8 bytes. Strings compare by content and order by their bytes. Lengths and offsets count bytes:

```stilt
fn main() / io {
  let word = "héllo"
  print("{word.len()} {word.chars().len()} {word < "help"}")
  print("{word.chars()}")
  print("brace: \{ quote: \" snowman: \u{2603}")
}
```

```output
6 5 false
["h", "é", "l", "l", "o"]
brace: { quote: " snowman: ☃
```

`é` takes two bytes, so `word.len()` is 6. `word.chars()` splits the string into its Unicode scalar values, each a `str` of its own, because there is no `char` type. A string can't be indexed: `word[0]` is E0317, *operator not defined on a type*. Use `word.slice(0, 1)` for bytes or `word.chars()` for scalar values. A slice that cuts a UTF-8 sequence panics with the kind `utf8-boundary`.

Every string literal interpolates, so a literal brace is written `\{`, and `{{` is E0006, *invalid escape*. [String interpolation](03-expressions.md#string-interpolation) covers the escapes and format specs.

`+` isn't defined on strings. Build a string with interpolation instead:

```stilt E0317:1
fn announce(name: str) / io { print("Go, " + name) }
```

The error offers the fix `"{a}{b}"`, which here is `"Go, {name}"`.

No method changes a string. `trim`, `replace` and the others return a new one ([The standard library](09-library.md)).

## Tuples

A tuple holds a fixed number of values of any types. `.0`, `.1` and so on read its elements, and a `let` can take it apart with a pattern. A tuple of one element has a trailing comma, `(x,)`, because `(x)` is `x` in parentheses:

```stilt
fn hp_range(hps: List<i64>) -> (i64, i64) {
  var low = hps[0]
  var high = hps[0]
  for hp in hps {
    low = low.min(hp)
    high = high.max(hp)
  }
  (low, high)
}

fn main() / io {
  let range = hp_range([30, 34, 32])
  let (low, high) = range
  print("{range} {range.0} {high - low} {(low,)}")
}
```

```output
(30, 34) 30 4 (30,)
```

A tuple type is written the same way: `(i64, i64)`, or `(i64,)` for one element.

## Lists

A `List<T>` holds any number of values of type `T`, in order. `xs[i]` reads element `i`, and panics with the kind `bounds` if there is none. If the index can be out of range, use `xs.get(i)`, which returns an `Option`:

```stilt
fn main() / io {
  var moves = ["Flame Pounce", "Root Snare"]
  moves.push("Bubble Jet")
  moves[1] = "Vine Whip"
  print("{moves} {moves.len()} {moves[2]} {moves.get(5)}")
}
```

```output
["Flame Pounce", "Vine Whip", "Bubble Jet"] 3 Bubble Jet None
```

A method named by a verb, such as `push` or `sort`, changes the list. So it needs a list you can change, such as a `var`. A method named by a participle, such as `sorted` or `reversed`, returns a new list and leaves the old one as it was. So do `map`, `filter` and `fold`, which keep the names other languages give them ([std.method-names](../../reference/17-std.md#std.method-names)). [The standard library](09-library.md) lists them all.

## Maps

A `Map<K, V>` maps keys of type `K` to values of type `V`, and always iterates in insertion order. So a program's output never depends on hashing. `m[k] = v` inserts or replaces, and `m.get(k)` returns an `Option`. `m[k]` reads a value, and panics with the kind `missing-key` if the key is absent and the map has no default:

```stilt
fn main() / io {
  var hp: Map<str, i64> = Map.new()
  hp["Mossling"] = 34
  hp["Embercat"] = 30
  hp["Mossling"] = 18
  print("{hp} {hp.get("Tidepup")} {hp["Embercat"]}")
}
```

```output
{"Mossling": 18, "Embercat": 30} None 30
```

A key that is already present keeps its place, so `Mossling` stays first. The key type must implement `Eq` and `Hash`, so floats can't be keys ([std.map-key-bounds](../../reference/17-std.md#std.map-key-bounds)).

`Map.with_default(d)` makes a map whose `m[k]` gives `d` for a missing key:

```stilt
fn main() / io {
  var wins: Map<str, i64> = Map.with_default(0)
  for winner in ["Embercat", "Mossling", "Embercat"] { wins[winner] += 1 }
  print("{wins}")
}
```

```output
{"Embercat": 2, "Mossling": 1}
```

`wins[winner] += 1` reads the default for a new name, then stores the sum, which inserts the key. Reading the default alone inserts nothing, and `get` still returns `None` for a missing key.

## Unit and `Never`

The unit type `()` has one value, also written `()`. A function with no return type returns it, and so do a block with no final expression and `print`.

`Never` has no values. An expression of type `Never` never finishes, so it fits wherever any type is expected. `return`, `raise`, `break` and `continue` have type `Never`, and so do calls to `panic`, `exit` and `unreachable`:

```stilt
fn health(hp: i64, max_hp: i64) -> f64 {
  let max = if max_hp > 0 { max_hp.to_f64() } else { panic("no maximum HP") }
  hp.to_f64() / max
}

fn main() / io {
  let done = print("{health(15, 30)}")
  print("{done}")
}
```

```output
0.5
()
```

The `else` branch has type `Never`, so it agrees with the `f64` of the other branch.

## `let` and `var`

`let` binds a name that can't change. `var` binds one that can, and so can every part of it: a field, a tuple element or a list element:

```stilt
type Element = | Fire | Water | Plant

type Creature = { name: str, element: Element, hp: i64, attack: i64 }

fn main() / io {
  let damage = 8
  var mossling = Creature { name: "Mossling", element: Plant, hp: 34, attack: 6 }
  mossling.hp -= damage
  var team = [mossling, mossling]
  team[1].name = "Mossling II"
  print("{mossling.hp} {team[1].name} {team[1].hp}")
}
```

```output
26 Mossling II 26
```

Changing a `let` binding, or any part of it, is E0403, *modifying what can't be modified*. That includes a call to a method that changes its receiver:

```stilt E0403:3
fn main() {
  let moves = ["Flame Pounce"]
  moves.push("Bubble Jet")
}
```

To change a value bound with `let`, bind it again with `var`, as in `var moves = moves`. [Scope and shadowing](03-expressions.md#scope-and-shadowing) says which binding a name refers to.

## Independent copies

Every value in core has **value semantics**: assigning a value, passing it to a parameter that isn't `inout`, binding it in a pattern and capturing it in a closure each make a copy. A change to the copy never shows in the original:

```stilt
type Element = | Fire | Water | Plant

type Creature = { name: str, element: Element, hp: i64, attack: i64 }

fn main() / io {
  var embercat = Creature { name: "Embercat", element: Fire, hp: 30, attack: 8 }
  var clone = embercat
  clone.hp -= 8
  let before = || embercat.hp
  embercat.hp = 0
  print("{embercat.hp} {clone.hp} {before()}")
}
```

```output
0 22 30
```

`clone` is a copy of `embercat`, and the closure `before` holds a copy taken when it was created. A value can change only through a name marked as changeable: a `var`, or an `inout` parameter ([Parameter modes](07-modes.md)). No two names in core share a value that changes.

Copies are cheap. The compiler shares strings, lists, maps and closures behind a reference count, and copies a shared value only when something writes to it. The language fixes only what a program observes ([values.independent-copies](../../reference/05-values.md#values.independent-copies)). So core has no `Copy` trait, no `.copy()` and no move errors.

## Type annotations

The compiler infers types inside each function body, from the signatures of the functions it calls. A signature always writes its types: every parameter's type, and the return type unless it is `()`. Inside a body, an annotation is optional, as in `let hp: u8 = 200` or `|name: str| name.len()`.

An expression never takes type arguments, so an annotation gives them instead: `let hp: Map<str, i64> = Map.new()`.

An annotation is needed when the compiler can't infer a type, which is E0312, *type that can't be inferred*. This happens when you use a value before anything has said what its type is: you call a method on it, read a field, index it or loop over it ([types.known-types](../../reference/07-types.md#types.known-types)). It also happens when the whole body leaves a type open, as `let xs = []` does if nothing ever adds to `xs`:

```stilt E0312:2
fn main() / io {
  let size = |s| s.len()
  print("{size("Embercat")}")
}
```

`s.len()` needs the type of `s`, and nothing before it says what that is. The call on line 3 comes too late. Annotate the parameter:

```stilt
fn main() / io {
  let size = |s: str| s.len()
  print("{size("Embercat")}")
}
```

```output
8
```

Because inference stays inside each body, changing one function's body never changes the types in another ([Inference](../../reference/07-types.md#inference)).
