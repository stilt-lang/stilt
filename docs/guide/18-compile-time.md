# Value parameters, staging, reflection and procedural macros

A type can take a number, as `List<T>` takes a type:

```stilt
use std.array

/// The total HP of a team of exactly `n` creatures.
fn total_hp<n: i64>(team: array.Array<i64, n>) -> i64 {
  var sum = 0
  for i in 0..n { sum += team[i] }
  sum
}

fn main() / io {
  let trio: array.Array<i64, 3> = [30, 34, 32]
  print("{total_hp(trio)} HP across {trio.len()} creatures")
}
```

```output
96 HP across 3 creatures
```

`Array<i64, 3>` holds exactly three numbers, so a function that takes one can't be given a team of two: the compiler rejects the call. `n` in `total_hp` is a **value parameter**, and the call finds it from the argument's type.

This chapter covers the `meta` tier: code that depends on what the compiler knows while it checks the program. Value parameters put sizes and moduli in types. `comptime` marks loops and branches that a release build can work out ahead of time. Reflection lets one function read the fields of any type, which is how `std.json` writes any record with nothing declared on it. Procedural macros run your code at compile time to write code.

A module that declares a value parameter, writes `comptime`, names `std.meta`, writes a bound test, declares a procedural macro or writes `quote` is a meta module. A module that only uses these, as `Array<i64, 3>`, `json.to_text(embercat)` or a macro, stays in its tier ([tiers](08-programs.md#module-headers-tiers-and-limits)).

## Value parameters

A function, a type or an impl can declare value parameters beside its type parameters, each written `name: T`. The name is lowercase, as every value's is. The type is an integer type or `bool`, whose values compare exactly; any other type, such as `f64` or `str`, is E0345. Inside the body, the name is an immutable value, as a constant is:

```stilt
type Mod<p: u64> = { value: u64 }

impl<p: u64> Mod<p> {
  fn plus(self, other: Mod<p>) -> Mod<p> { Mod { value: (self.value + other.value) % p } }
  fn modulus(self) -> u64 { p }
}

const PRIME: u64 = 1_000_000_007

fn main() / io {
  let a: Mod<PRIME> = Mod { value: 5 }
  let b: Mod<1_000_000_007> = Mod { value: PRIME - 1 }
  let c = a.plus(b)
  print("{c.value} mod {c.modulus()}")
}
```

```output
4 mod 1000000007
```

A **value argument** is what a type with value parameters takes in each value position: an integer literal, `true` or `false`, a constant, or a value parameter in scope ([value arguments](../../reference/07-types.md#generics.value-arguments)). Arithmetic, as in `Array<i64, n + 1>`, is a syntax error. A literal out of the parameter type's range is E0320. A type where a value belongs, as `Mod<i64>`, or a value where a type belongs, as `List<3>`, is E0347.

Two types are equal when their arguments are equal by value, so `Mod<PRIME>` and `Mod<1_000_000_007>` above are one type. A value parameter is equal only to itself, whatever value the calls give it. In this body, `n` might be 3 at every call, and still `Array<i64, n>` isn't `Array<i64, 3>`:

```stilt E0311:4
use std.array

fn sum3<n: i64>(a: array.Array<i64, n>) -> i64 {
  let b: array.Array<i64, 3> = a
  b[0] + b[1] + b[2]
}

fn main() {}
```

A binding in the body can't take a value parameter's name: a `let`, a parameter or a closure's parameter named `p` inside `plus` is E0348.

## Value arguments in calls

A call writes no value arguments. The compiler finds them as it finds type arguments: from the types of the call's arguments, and from the type the call is expected to have. A record literal finds them from its expected type, as `Mod { value: 5 }` does above:

```stilt
use std.array

fn dot<n: i64>(a: array.Array<i64, n>, b: array.Array<i64, n>) -> i64 {
  var sum = 0
  for i in 0..n { sum += a[i] * b[i] }
  sum
}

fn main() / io {
  let v: array.Array<i64, 3> = [1, 2, 3]
  let ones: array.Array<i64, 3> = array.fill(1)
  print("{dot(v, v)} {dot(v, ones)}")
}
```

```output
14 6
```

So a function's value parameter must appear in one of its parameter types or in its result type, or nothing could give it a value: one that doesn't is E0346. An impl's type names each of the impl's parameters once, so `impl Mod<7>` is E0302. A call that still leaves a value parameter unknown is E0312, as for a type parameter. Here nothing says how long the array is:

```stilt E0312:4
use std.array

fn main() {
  let z = array.fill(0)
}
```

One body of `dot` serves every length. A debug build passes `n` as a hidden argument, and a release build makes a copy of `dot` for each length the program uses ([how value parameters are compiled](../../reference/rationale/07-types.md#value-parameters)).

## Arrays

`std.array` declares `Array<T, n: i64>`: exactly `n` values of type `T`, stored inline, as a record's fields are. It isn't in the prelude, so a module writes `use std.array` and names the type `array.Array<i64, 3>`. A list literal where an array is expected makes an array:

```stilt
use std.array

fn main() / io {
  let hp: array.Array<i64, 3> = [30, 34, 32]
  var healed = hp
  healed[0] = 40
  let [first, _, last] = hp
  print("{hp} {healed} {first + last}")
  print("{hp.map(|h| h * 2)} {hp == [30, 34, 32]} {hp.to_list().len()}")
  let pair: Option<array.Array<i64, 2>> = array.from_list([30, 34, 32])
  print("{pair}")
}
```

```output
[30, 34, 32] [40, 34, 32] 62
[60, 68, 64] true 3
None
```

An array is a value, so changing `healed` leaves `hp` as it was. `a[i]` reads and writes an element, and panics with `bounds` outside `0..n`, as a list's index does. `for` yields the elements in order. An array has `len`, `to_list` and `map`, and nothing else, so `a.push(1)` is E0314 ([arrays](../../reference/07-types.md#generics.arrays)). `array.fill(x)` makes `n` copies of `x`, and `array.from_list(xs)` gives `None` unless `xs` has exactly `n` elements. Arrays compare, hash and print as lists do.

A literal's length must be the size, or it is E0311, which names both lengths:

```stilt E0311:4
use std.array

fn main() {
  let v: array.Array<i64, 3> = [1, 2]
}
```

A list literal is an array only where an array is expected. So `hp == [30, 34, 32]` compares two arrays, while in `[30, 34, 32] == hp` the literal is a `List`, and `hp` is E0311 ([array literals](../../reference/07-types.md#generics.array-literals)).

A list pattern matches an array when its length fits the size, which the compiler checks. So `let [first, _, last] = hp` needs no `else`. A pattern that doesn't fit is E0311, and so is a rest that binds a name, as `[x, ..rest]` ([array patterns](../../reference/07-types.md#generics.array-patterns)).

Making, copying, reading and writing an array allocate nothing. Only `to_list` and the calls of the function given to `map` add `alloc`.

## Staging annotations

A **staging annotation** is `comptime` before a `for`, an `if` or a `match`. It says that what controls the form is known at compile time, so a release build can unroll the loop or keep only one branch:

```stilt
use std.array

fn dot<n: i64>(a: array.Array<i64, n>, b: array.Array<i64, n>) -> i64 {
  var sum = 0
  comptime for i in 0..n { sum += a[i] * b[i] }
  sum
}

fn size<n: i64>(a: array.Array<i64, n>) -> str {
  comptime if n == 0 { "empty" } else if n <= 4 { "small" } else { "large" }
}

fn main() / io {
  let v: array.Array<i64, 3> = [1, 2, 3]
  let big: array.Array<i64, 5> = array.fill(1)
  print("{dot(v, v)} {size(v)} {size(big)}")
}
```

```output
14 small large
```

The annotation changes nothing else. Deleting every `comptime` from a program that has no error changes nothing it does, and a debug build runs each form as if the annotation weren't there ([erasure](../../reference/16-meta.md#meta.erasure)). The body of a `comptime for`, and the branches and arms of the others, are ordinary code. They can read anything in scope, print, `break` and `return`.

A chain of `if`s takes the annotation once, before its first `if`, so `else comptime if` is a syntax error. So is `comptime` before a `while`, a `let` or a block.

What `comptime` controls must be **static**: known without running the program. Literals, constants, value parameters and the variables an annotation binds are static, and so are a `let` of a static value and anything built from static values with operators, fields, tuples and lists. A call is static when its arguments are and its row is empty: `n.count_ones()` is, and `print(1)` isn't ([static expressions](../../reference/16-meta.md#meta.static-expressions)). A function's parameter, a `var` and a closure aren't. An annotated part that isn't static is E0349, which says why:

```stilt E0349:2
fn count(xs: List<i64>) / io {
  comptime for x in xs { print("{x}") }
}

fn main() / io { count([1, 2]) }
```

A static expression can still panic, as `n / 0` does. It panics where the run reaches it, never while the program is built or checked.

## Shapes

A generic function knows its type only through its bounds. To print, compare or encode a record it has never seen, it reads the type's **shape** instead. In a module that writes `use std.meta`, `T.shape()` is the shape of the type `T`: an ordinary value, of type `meta.Shape<T>`, whose case says what kind of type `T` is. `T.name()` is the type's name, as `"Creature"` or `"List<i64>"`. This `describe` turns any creature into text without knowing its fields:

```stilt
use std.meta

type Element = | Fire | Water | Plant
type Creature = { name: str, element: Element, hp: i64, attack: i64 }

/// Any value as text, read through its type's shape.
fn describe<T>(value: T) -> str {
  comptime match T.shape() {
    Int(n) => n.text(value)
    Str(c) => c.get(value)
    Record(fields) => {
      var parts: List<str> = []
      comptime for f in fields { parts.push("{f.name()}={describe(f.get(value))}") }
      "\{{", ".join(parts)}}"
    }
    Variants(cases) => {
      var text = ""
      comptime for c in cases {
        if c.get(value).is_some() { text = c.name() }
      }
      text
    }
    _ => T.name()
  }
}

fn main() / io {
  print(describe(Creature { name: "Embercat", element: Fire, hp: 30, attack: 8 }))
}
```

```output
{name=Embercat, element=Fire, hp=30, attack=8}
```

A function that names `T.shape()` **reflects** on `T`. Each case of the shape gives an accessor, which reads values of `T` ([shape accessors](../../reference/16-meta.md#meta.shape-accessors)). A type's shape is the first case of this table that fits it:

| Case | Types | The accessor gives |
| --- | --- | --- |
| `Int(n)` | Every integer type | `n.text(value)`, and `n.parse(text)`, an `Option<T>` |
| `Float(c)` | `f32`, `f64` | `c.get(value)`, an `f64`, and `c.make(x)` |
| `Bool(c)`, `Str(c)`, `Unit(c)` | `bool`, `str`, `()` | `get` and `make` |
| `Option(c)` | `Option<E>` | `get` and `make`, as an `Option<E>` |
| `List(c)`, `Set(c)` | `List<E>`, `Set<E>` | `get` and `make`, as a `List<E>` |
| `Map(c)` | `Map<K, V>` | `get` and `make`, as a `List<(K, V)>` |
| `Array(a)` | `array.Array<E, n>` | `get`, `make` and `len` |
| `Tuple(fields)`, `Record(fields)` | Tuples and records | The fields, in order |
| `Variants(cases)` | Declared variant types | The cases, in order |

`Option` comes before `Variants`, so `Option<Creature>` is an `Option`, and `Result` is a `Variants`. A record's fields come in the order of its declaration, and an anonymous record's in alphabetical order. Function types, handler types, and native types such as `View`, `Lazy` and `Shared` have no shape. A shape gives every field, private ones included.

If a type has its own member named `shape` or `name`, `T.shape()` calls that one first. In a module that doesn't write `use std.meta`, `T.shape()` is E0314 for a type with no such member.

## Fresh types

No arm learns what `T` is: in the `Int` arm above, `T` is still the type parameter, and the arm reads `value` through `n`. The type of a field, of an element or of a case's payload is a **fresh type**: a type of its own in its arm or loop body, with no bound, which code there can't name. It can only pass such a value to a generic function, as `describe(f.get(value))` gives each field's value to `describe`, which reflects on its type in turn. So the generic body is still checked once, before anything calls it.

A value whose type holds a fresh type can't leave its arm or loop body: returning it, raising it, or storing it in a variable declared outside is E0351. Here `all` is declared outside the arm, so pushing `x` into it is an error:

```stilt E0351:6
use std.meta

fn elements<T>(value: T) {
  var all = []
  match T.shape() {
    List(c) => { for x in c.get(value) { all.push(x) } }
    _ => {}
  }
}

fn main() {}
```

A fresh type has no bound, so `x == y` on two values of one is E0318, as for any type parameter without `Eq`.

`for` or `comptime for` over a record's or a tuple's `fields` binds each field in turn. A field has `f.name()`, `f.index()`, counted from 0, and `f.get(value)`. `fields.build(f)` goes the other way: it makes a `T` from the value that `f` gives for each field, in order. Here it makes an empty character sheet:

```stilt
use std.meta

type Sheet = { name: str, hp: i64, attack: i64 }

fn blank<T>() -> T / raise<str> {
  match T.shape() {
    Int(n) => n.parse("0") else raise "no zero"
    Str(c) => c.make("")
    Record(fields) => try fields.build(|f| try blank())
    Tuple(fields) => try fields.build(|f| try blank())
    _ => raise "no blank {T.name()}"
  }
}

fn main() / {io, raise<str>} {
  let sheet: Sheet = try blank()
  let pair: (i64, str) = try blank()
  print("{sheet} {pair}")
}
```

```output
Sheet { name: "", hp: 0, attack: 0 } (0, "")
```

The function given to `build` must work for a field of any type, so it is a polymorphic argument: a generic function, a closure literal or a parameter passed on ([polymorphic arguments](14-polymorphism.md)). Its effects pass through, and once one call raises, `build` calls it on no later field ([building](../../reference/16-meta.md#meta.building)).

A variant type's `cases` works the same way. `c.get(value)` is `Some` of the payload when `value` is that variant, and `None` otherwise, and `c.make(payload)` makes the variant. A payload is a tuple: `()` for a variant without one.

## Bound tests

A **bound test**, `if T: Show { … }`, asks whether the type behind `T` has an impl. Inside its branch, `T` has the bound, so `"{value}"` uses the type's own `Show`:

```stilt
use std.meta

type Element = | Fire | Water | Plant
type Ability = { name: str, boost: fn(i64) -> i64 }

fn label<T>(value: T) -> str {
  if T: Show { "{value}" } else { "<{T.name()}>" }
}

fn main() / io {
  let rage = Ability { name: "Rage", boost: |attack| attack * 2 }
  print("{label(42)}, {label(Fire)}, {label(rage)}, {label([rage])}")
}
```

```output
42, Fire, <Ability>, <List<Ability>>
```

`Ability` has no `Show`, because a function has none, and so `List<Ability>` has none either. The `else` branch learns nothing about `T`. A bound test is the whole condition of an `if` or an `else if`, so `a && T: Show` is a syntax error. A `T` that isn't a type parameter in scope is E0212:

```stilt E0212:4
type Element = | Fire | Water | Plant

fn main() / io {
  if Element: Show { print("shown") }
}
```

A bound test is static, and so are `T.shape()`, `T.name()`, `fields`, `cases`, and a field's or a case's name and index. That is why `comptime match T.shape()` and `comptime for f in fields` are valid above. A list's elements aren't static, so a `comptime for` over what a `List` arm gives is E0349 ([static reflection](../../reference/16-meta.md#meta.static-reflection)).

## What reflects

Where a function that reflects is called, the type it gets must have a shape. No bound says that a function reflects. `stilt show` prints `reflects T` in the brackets of facts after the signature. A function that gives the fresh types of its shape to one that reflects, as `describe` does, reflects **on the parts** of `T`. Then every type that `T` holds, at any depth, needs a shape too. The first that has none is E0350:

```stilt E0350:18
use std.meta

fn size<T>(value: T) -> i64 {
  match T.shape() {
    Record(fields) => {
      var n = 0
      for f in fields { n += size(f.get(value)) }
      n
    }
    _ => 1
  }
}

type Ability = { name: str, boost: fn(i64) -> i64 }

fn main() / io {
  let rage = Ability { name: "Rage", boost: |attack| attack * 2 }
  print("{size(rage)}")
}
```

The message names the type `fn(i64) -> i64`, the field `boost` that holds it, and the chain of functions that reflect. A generic function that passes its own type parameter to `size` reflects in turn, so the error lands where the type is first written ([types without a shape](../../reference/16-meta.md#meta.types-without-shape)).

The traits that a function's bound tests name are its **guards**. A type with an impl of a guard needs no shape, and the walk skips it and what it holds. This is how `std.json` writes a type that holds a function but implements `ToJson`.

A debug build compiles one copy of each function that reflects, which serves every type, and a release build makes a copy for each type ([how reflection is compiled](../../reference/rationale/16-meta.md#what-reflects)).

## JSON

`std.json` is written in Stilt on `std.meta`. `json.to_text` writes any value whose type has a shape, and `json.from_text` reads one back, with nothing declared on the type:

```stilt exit:1
use std.json

type Element = | Fire | Water | Plant
type Creature = { name: str, element: Element, hp: i64, attack: i64 }

fn main() / {io, raise<json.Error>} {
  let embercat = Creature { name: "Embercat", element: Fire, hp: 30, attack: 8 }
  let text = json.to_text(embercat)
  print(text)
  let back: Creature = try json.from_text(text)
  print("{back == embercat}")
  let broken: Creature = try json.from_text("\{\"name\": \"Mossling\", \"element\": \"Plant\", \"attack\": 6}")
  print("{broken}")
}
```

```output
{"name":"Embercat","element":"Fire","hp":30,"attack":8}
true
```

```stderr
error: Missing("$.hp")
```

The JSON follows the shape ([writing](../../reference/17-std.md#std.json-writing)):

| Value | JSON |
| --- | --- |
| An integer or a float | A number |
| `bool`, `str` | `true` or `false`, a string |
| `()`, `None` | `null`; `Some(x)` is the JSON of `x` |
| A list, a set, an array or a tuple | An array |
| A record | An object with a member for each field |
| A map | An object when its keys are strings, and otherwise an array of `[key, value]` arrays |
| A variant | Its name as a string, or `{"Name": [payload…]}` when it has a payload |

Reading follows the same table. A missing field raises `Missing(path)`, unless its type is an `Option`, which reads as `None`. Anything else that doesn't fit raises `Mismatch(path, expected, found)`, as `Mismatch("$.level", "u8", "300")` when a `u8` field `level` holds `300` ([reading](../../reference/17-std.md#std.json-reading)).

A type that needs other JSON implements `json.ToJson` or `json.FromJson`, which the writers and readers use at any depth. `json.Value` is the JSON tree between the text and the types, `json.parse` reads text into one, raising `Syntax(line, column)` at the first character that can't continue, and `json.render` writes one with no whitespace:

```stilt
use std.json

type Element = | Fire | Water | Plant

impl json.ToJson for Element {
  fn to_json(self) -> json.Value {
    json.Text(match self { Fire => "fire", Water => "water", Plant => "plant" })
  }
}

type Move = { name: str, element: Element, power: i64 }

fn main() / io {
  print(json.to_text(Move { name: "Flame Pounce", element: Fire, power: 40 }))
  print("{Result.of(|| try json.parse("[1,\n 2,,]"))}")
}
```

```output
{"name":"Flame Pounce","element":"fire","power":40}
Err(Syntax(2, 4))
```

## Procedural macros

A pattern macro substitutes tokens and runs nothing ([pattern macros](16-macros.md)). A **procedural macro** is a function that runs while the program is checked: it takes the tokens of a use and gives back code. Use one for what substitution can't do, such as a notation that has to be parsed. This one reads arithmetic in reverse Polish notation:

```stilt
use std.meta

/// `rpn!(w h * 2 /)`: arithmetic in reverse Polish notation, over names and
/// integers.
pub macro rpn(ts: meta.Tokens) -> meta.Expr / raise<meta.Error> {
  var stack: List<meta.Expr> = []
  for t in ts.items {
    match t.kind() {
      Number(digits) => {
        let Some(n) = digits.to_i64() else raise meta.error(t.span(), "expected an `i64`")
        stack.push(quote { $n })
      }
      Word(_) => {
        let Some(name) = t.name() else raise meta.error(t.span(), "expected a name")
        stack.push(quote { $name })
      }
      Punct(op) => {
        let Some(b) = stack.pop() else raise meta.error(t.span(), "`{op}` needs two operands")
        let Some(a) = stack.pop() else raise meta.error(t.span(), "`{op}` needs two operands")
        stack.push(try operator(t, op, a, b))
      }
      _ => raise meta.error(t.span(), "expected a name, an integer or an operator")
    }
  }
  if stack.len() != 1 { raise meta.error(ts.close, "this leaves {stack.len()} values, not one") }
  stack[0]
}

fn operator(t: meta.Token, op: str, a: meta.Expr, b: meta.Expr) -> meta.Expr / raise<meta.Error> {
  match op {
    "+" => quote { $a + $b }
    "-" => quote { $a - $b }
    "*" => quote { $a * $b }
    "/" => quote { $a / $b }
    _ => raise meta.error(t.span(), "`{op}` isn't an operator")
  }
}

fn main() {}
```

`macro` declares a procedural macro as `fn` declares a function. Each parameter's type says what a use gives it ([declarations](../../reference/16-meta.md#macros.procedural-declarations)):

| Type | A use gives |
| --- | --- |
| `meta.Expr`, `meta.Pattern`, `meta.Type` | An expression, a pattern or a type, parsed whole |
| `meta.Text` | A string literal |
| `meta.File` | A file that a string literal names |
| `meta.Tokens` | The tokens themselves; only the last parameter can take them |

The result is a `meta.Expr`, a `meta.Pattern` or a `meta.Type`, so a macro writes an expression, a pattern or a type, and never an item. A macro does no input or output: its row is empty or `raise<meta.Error>`, so a call in it that prints or reads a file is E0502. It can allocate and panic. Generics, a `without` clause, or a parameter, result or row of another type are E0228:

```stilt E0228:3
use std.meta

macro twice<T>(e: meta.Expr) -> meta.Expr { quote { $e * 2 } }

fn main() {}
```

Another module imports procedural macros with `meta use`, and uses one as a pattern macro is used:

```stilt fragment
meta use calc

/// The damage of a move of `power` from a creature with `attack`.
fn damage(attack: i64, power: i64) -> i64 { calc.rpn!(attack power * 10 /) }
```

`meta use calc` gives `calc`'s procedural macros and nothing else of the module, whose compile-time code isn't part of the program. `use calc` gives its other items, pattern macros included, and a module can write both. A procedural macro can't be used in its own module: `rpn!(…)` there is E0212 ([`meta use`](../../reference/16-meta.md#macros.meta-use)).

## Quotes

A macro builds code from **quotes**, never from strings. `quote { … }` is a `meta.Expr`. `quote type { … }`, `quote pattern { … }` and `quote field { … }` make a type, a pattern and one field of a record literal. In a quote, `$x` **splices** in a value of the macro's code, and `$(e)` any expression:

- A `meta.Expr`, `meta.Pattern` or `meta.Type` stands where that form goes, as one form, as if in parentheses.
- A `meta.Name` stands wherever a name goes.
- A `str`, an integer, a `bool` or a float stands as a literal of its value.
- `$..xs` spreads a `List` of these among the elements of a list, a tuple or a call's arguments, or a `List<meta.FieldInit>` among a record literal's fields.

A splice of another type, or in another place, is E0311 ([splices](../../reference/16-meta.md#macros.splices)). A list needs `..`, so `[$xs]` for a `List<i64>` is an error:

```stilt E0311:5
use std.meta

fn listed() -> meta.Expr {
  let xs = [1, 2, 3]
  quote { [$xs] }
}

fn main() {}
```

A quote is hygienic, as a pattern macro's template is. A name it binds is fresh in each expansion, so it never captures a name written at the use. Every other name it writes is found where the quote is written, among the items and imports of the macro's module ([quote hygiene](../../reference/16-meta.md#macros.quote-hygiene)). A local of the macro's own code is not among them, so naming one without `$` is E0211:

```stilt E0211:5
use std.meta

fn plus_one() -> meta.Expr {
  let n = 3
  quote { n + 1 }
}

fn main() {}
```

There is no way to break hygiene, so a name that the code at the use must see is passed in. `t.name()` of a token is the name as written at the use: spliced as a binding, it binds that name there, where the code after the use sees it. `meta.fresh(text)` makes a name equal to no other, which several quotes can share, one binding it and another naming it:

```stilt
use std.meta

/// `e`, computed once and doubled, through a fresh name.
fn doubled(e: meta.Expr) -> meta.Expr {
  let v = meta.fresh("v")
  let sum = quote { $v + $v }
  quote {
    let $v = $e
    $sum
  }
}

fn main() / io {
  let code = doubled(quote { 21 })
  let name = meta.fresh("total")
  print("{name.text()}")
}
```

```output
total
```

`doubled` is an ordinary function, which a macro can call while it runs, and which this program calls when it runs. Outside a macro, a quote still makes its code, but nothing of it can be seen except a name's `text()` ([outside a run](../../reference/16-meta.md#macros.outside-run)).

## Uses and expansion

A use's group is split at its commas into **parts**, which go to the parameters in order. A trailing block goes to the last parameter, and a last `meta.Tokens` parameter takes every part that's left. A part that doesn't fit its parameter, one too many or one too few is E0227 ([parts](../../reference/16-meta.md#macros.parts)). A use where its result's form can't stand, such as an expression macro in a pattern, is E0223.

A macro reads tokens with `meta.cursor`, written in Stilt. Its methods read a word, a punctuation mark, a name, a string, a number or a group, and `expr`, `pattern` and `type_` parse a whole form with the language's own parser. Each one raises a `meta.Error` at the token it found when that isn't what it expected ([cursor](../../reference/16-meta.md#macros.cursor)).

A use expands when its module is checked. The macro runs once, with the use's parts, and its result replaces the use and is checked as code written there. Its effects belong to the using function, which a `without` limits. A macro sees only its parts and the files they name, so the same use always expands to the same code. Uses inside an expansion expand in turn. One nested too deep is E0224, and a use whose expansions grow too large is E0231 ([expansions](../../reference/16-meta.md#macros.nested-expansions)).

Errors point at the tokens written at the use:

- A macro that raises `meta.error(span, message)` gives E0225 at that span. So `calc.rpn!(attack *)` is an error at `*` that says "`*` needs two operands".
- A macro that runs too long, recurses too deep, runs out of memory, panics or calls C stops, with E0226 at the use ([step limits](../../reference/16-meta.md#macros.step-limits)).
- A use that fails reports nothing more, and a macro whose own module has an error expands no use.

A `meta.File` part names a file by a path relative to the package's manifest, or to the program's root file when there is no manifest. The compiler reads the file, so a macro reads nothing itself, and an edit of the file expands the uses that name it again. A path that leaves the package, or names no UTF-8 file, is E0229 ([named files](../../reference/16-meta.md#macros.named-files)).

`stilt show` prints a use as written. `stilt show --expanded` prints its expansion in its place, with each fresh name followed by `#` and a number, as `v#1`, and the language server shows the expansion on hover.
