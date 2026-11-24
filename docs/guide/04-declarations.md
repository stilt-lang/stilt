# Declaring types

Here are the arena's types, and a function that takes a creature apart:

```stilt
type Element = | Fire | Water | Plant

type Creature = { name: str, element: Element, hp: i64, attack: i64 }

fn status(c: Creature) -> str {
  match c {
    Creature { hp: 0, name, .. } => "{name} has fainted"
    Creature { name, element: Fire, .. } => "{name} is burning to fight"
    Creature { name, hp, .. } => "{name} has {hp} HP"
  }
}

fn main() / io {
  let embercat = Creature { name: "Embercat", element: Fire, hp: 30, attack: 8 }
  let mossling = Creature { name: "Mossling", element: Plant, hp: 34, attack: 6 }
  print(status(embercat))
  print(status(mossling))
  print(status(Creature { ..mossling, hp: 0 }))
}
```

```output
Embercat is burning to fight
Mossling has 34 HP
Mossling has fainted
```

`Element` is a variant type and `Creature` is a record: the two kinds of type a program declares. `match` compares the creature with each pattern in turn, and a pattern can look inside a record's fields. `Creature { ..mossling, hp: 0 }` builds a copy of `mossling` with one field changed.

## Records

A **record** is a value with named fields. `type Name = { field: T, … }` declares a record type, and a literal gives every field a value, in any order:

```stilt
type Element = | Fire | Water | Plant

type Creature = { name: str, element: Element, hp: i64, attack: i64 }

fn main() / io {
  let name = "Tidepup"
  let tidepup = Creature { name, element: Water, hp: 32, attack: 7 }
  var hurt = tidepup
  hurt.hp = 12
  print("{tidepup.name} has {tidepup.hp} HP, its copy has {hurt.hp}.")
  print("{Creature { ..tidepup, attack: 9 }}")
}
```

```output
Tidepup has 32 HP, its copy has 12.
Creature { name: "Tidepup", element: Water, hp: 32, attack: 9 }
```

`tidepup.hp` reads a field, and `hurt.hp = 12` assigns to a field of a `var`. A field whose value is a variable of the same name is written once: `Creature { name, … }` is short for `Creature { name: name, … }`. Assigning a record copies it, so changing `hurt` leaves `tidepup` as it was ([Values and types](02-values.md)).

`Creature { ..tidepup, attack: 9 }` is an **update**: a copy of `tidepup` with the fields written after it changed. An update can't add or remove a field, so its result always has the type of the record after `..` ([records.update-fields](../../reference/07-types.md#records.update-fields)).

A literal must give every field exactly once. A field left out or given twice is E0316, *field given twice or left out*:

```stilt E0316:5
type Element = | Fire | Water | Plant

type Creature = { name: str, element: Element, hp: i64, attack: i64 }

fn egg() -> Creature { Creature { name: "Egg", element: Fire, hp: 1 } }
```

Reading a field the record doesn't have is E0313, *no such field*. A record type's name isn't a value, so `Creature(…)` is E0212, *wrong kind of name* ([declarations.wrong-kind-of-name](../../reference/10-declarations.md#declarations.wrong-kind-of-name)). A record may have no fields, as in `type Marker = {}`.

A `{` starts a record literal only after an uppercase name, `Self`, or a path that ends in one, such as `arena.Creature`. In the head of an `if`, `while`, `match` or `for`, the first `{` always opens the body, so a literal there goes in parentheses ([expressions.struct-literals](../../reference/08-expressions.md#expressions.struct-literals)).

Records are **nominal**: a record type is its declaration, not its list of fields. Two record types with the same fields are different types, and a function that takes a `Creature` takes nothing else. A function over any record with a `name` field, or a record type written inline, belongs to the advanced tier ([Records and variadic generics](15-records.md)).

## Variant types

A **variant type** has values that are each exactly one of its variants. A variant can carry a payload of one or more fields, matched by position:

```stilt
type Element = | Fire | Water | Plant

type Move = { name: str, element: Element, power: i64 }

/// What a creature does on its turn.
type Action = | Strike(Move) | Heal(amount: i64) | Flee

fn describe(action: Action) -> str {
  match action {
    Strike(m) => "uses {m.name}"
    Heal(n) => "heals {n} HP"
    Flee => "runs away"
  }
}

fn main() / io {
  let pounce = Move { name: "Flame Pounce", element: Fire, power: 40 }
  for action in [Strike(pounce), Heal(5), Flee] { print(describe(action)) }
  print("{[5, 10].map(Heal)}")
}
```

```output
uses Flame Pounce
heals 5 HP
runs away
[Heal(5), Heal(10)]
```

These rules decide how variants are written and used:

- **Payloads.** The name in `Heal(amount: i64)` documents the field and appears nowhere else: constructors and patterns are positional. A variant written with parentheses has at least one field, so `Flee()` in a declaration is a syntax error, E0100.
- **The first `|`** is optional when the type has two or more variants, and required when it has one.
- **Constructors.** A variant with a payload is a function, so `Heal` can be passed to `map` as a `fn(i64) -> Action`. A variant without one is a value, so calling it, as in `Flee()`, is E0311, *mismatched types* ([declarations.constructors](../../reference/10-declarations.md#declarations.constructors)).

`Option`, `Result` and `Ordering` are ordinary variant types, declared in the prelude ([The standard library](09-library.md)).

## Namespaces and newtypes

A module keeps types and values apart. The **type namespace** holds types and traits, and the **value namespace** holds variants, functions, constants and imported modules. A name is defined once in each, so two variants named `Fire` in one module are E0208, *name defined twice*, even in different types.

Because the namespaces are separate, a variant can share its type's name. A type with one such variant is a **newtype**, a distinct type that wraps another:

```stilt
type CreatureId = | CreatureId(i64)

type MoveId = | MoveId(i64)

fn lookup(id: CreatureId) -> str {
  let CreatureId(n) = id
  "creature #{n}"
}

fn main() / io {
  print(lookup(CreatureId(3)))
  print("{MoveId(3)}")
}
```

```output
creature #3
MoveId(3)
```

`CreatureId` and `MoveId` both hold an `i64`, and they are still different types. Passing one for the other is E0311, *mismatched types*:

```stilt E0311:10
type CreatureId = | CreatureId(i64)

type MoveId = | MoveId(i64)

fn lookup(id: CreatureId) -> str {
  let CreatureId(n) = id
  "creature #{n}"
}

fn main() / io { print(lookup(MoveId(3))) }
```

Where a name stands decides which namespace it is read in. `Name {` names a record type, while `Name(…)` and a bare `Name` name a value. In `Name.member`, `Name` is read as a type first, so `CreatureId.new(…)` calls an associated function of the type ([declarations.name-lookup](../../reference/10-declarations.md#declarations.name-lookup)).

An expression in another module names a variant with its module, as in `arena.Fire`. The prelude's variants, such as `Some` and `Ok`, need no module ([Programs](08-programs.md)), and neither does a pattern ([Patterns](#patterns)).

## Generic types

A record or variant type can take **type parameters**, uppercase names written after the type's name. A type can also contain itself:

```stilt
/// A tournament: one entrant, or a final between the winners of two smaller ones.
type Bracket<T> = | Entrant(T) | Final(Bracket<T>, Bracket<T>)

fn names(b: Bracket<str>) -> List<str> {
  match b {
    Entrant(name) => [name]
    Final(left, right) => names(left).concat(names(right))
  }
}

fn main() / io {
  let bracket = Final(Entrant("Embercat"), Final(Entrant("Mossling"), Entrant("Tidepup")))
  print("{names(bracket)}")
  print("{bracket}")
}
```

```output
["Embercat", "Mossling", "Tidepup"]
Final(Entrant("Embercat"), Final(Entrant("Mossling"), Entrant("Tidepup")))
```

A type written in a signature or a field gives every type argument, as in `Bracket<str>` or `List<i64>`, and any other count is E0300, *wrong number of type arguments*. Expressions and patterns write the type's name alone, and inference finds the arguments, as `Entrant("Embercat")` does. A type's parameters take no bounds, so `type Ranked<T: Ord>` is a syntax error, E0100. Bounds go on functions and `impl` blocks ([Traits and generics](06-traits.md#bounds)).

A recursive type needs no box. A record that contains itself through record fields and tuples alone could never be built, and declaring one is E0309, *record that contains itself*:

```stilt E0309:1
type Chain = { creature: str, next: Chain }
```

`next: Option<Chain>` or `next: List<Chain>` gives the chain a way to end, and is accepted ([declarations.recursive-types](../../reference/10-declarations.md#declarations.recursive-types)).

## Constants

`const NAME: T = e` declares a constant. Its name is uppercase, and its type is always written:

```stilt
type Element = | Fire | Water | Plant

type Move = { name: str, element: Element, power: i64 }

const MAX_HP: i64 = 99

const FLAME_POUNCE: Move = Move { name: "Flame Pounce", element: Fire, power: 40 }

const STARTERS: List<str> = ["Embercat", "Mossling", "Tidepup"]

fn main() / io { print("{FLAME_POUNCE.name} {STARTERS} {MAX_HP} {i64.MAX}") }
```

```output
Flame Pounce ["Embercat", "Mossling", "Tidepup"] 99 9223372036854775807
```

A constant's value is a **constant expression**: literals, unary `-`, other constants, and tuples, lists, records and variants built from those. Anything else, such as arithmetic, a call or an interpolated string, is E0326, *constant's value isn't a constant expression*:

```stilt E0326:1
const MAX_HP: i64 = 3 * 33
```

Constants can refer to one another, but not in a cycle, which is E0327, *constants in a cycle*. A constant is evaluated the first time the program uses it ([declarations.constant-evaluation](../../reference/10-declarations.md#declarations.constant-evaluation)). A constant can also belong to a type, declared in its `impl` block and read as `Type.NAME`, as `i64.MAX` is ([Inherent methods](06-traits.md#inherent-methods)). Because a constant's name is uppercase, it can stand in a pattern ([Patterns](#patterns)).

## Functions

A function declaration has this form, and every part but the name, the parameters and the body can be left out:

```stilt fragment
pub fn name<Generics>(params) -> ReturnType / row without limits { body }
```

These are the parts:

- **Parameters** are written `name: T`, or `inout name: T` for one that changes the caller's place ([Parameter modes](07-modes.md)). A parameter is a name, never a pattern. A parameter of function type that the function keeps is written `escaping name: fn(…)` ([Errors and effects](05-errors.md#effects-that-pass-through)).
- **The return type** is `()` when it is left out.
- **Generics** are type parameters, which can carry bounds, as in `<T: Ord + Show>` ([Traits and generics](06-traits.md)).
- **The row** after `/` lists the effects the function performs, such as `io` or `raise<E>` ([Errors and effects](05-errors.md)).
- **Limits** after `without`, such as `panic` or `alloc`, are facts the body must not have, including through the functions it calls ([Errors and effects](05-errors.md#limits)). The clause can end the signature's line or start the next one ([declarations.limits](../../reference/10-declarations.md#declarations.limits)).
- **The body** is a block, and its last expression is the result ([Expressions](03-expressions.md#blocks-and-statements)).

Here are two functions, one that returns early and one that prints:

```stilt
type Element = | Fire | Water | Plant

type Creature = { name: str, element: Element, hp: i64, attack: i64 }

fn average_hp(team: List<Creature>) -> i64 {
  if team.is_empty() { return 0 }
  team.fold(0, |sum, c| sum + c.hp) / team.len()
}

fn report(label: str, team: List<Creature>) / io { print("{label}: {average_hp(team)} HP") }

fn main() / io {
  let embercat = Creature { name: "Embercat", element: Fire, hp: 30, attack: 8 }
  let mossling = Creature { name: "Mossling", element: Plant, hp: 34, attack: 6 }
  let tidepup = Creature { name: "Tidepup", element: Water, hp: 32, attack: 7 }
  report("nobody", [])
  report("starters", [embercat, mossling, tidepup])
}
```

```output
nobody: 0 HP
starters: 32 HP
```

A signature is always written in full: each parameter's type, and the return type unless it is `()`. Inside a body, types are inferred, but only from the signatures of what the body uses, never from another body ([Expressions](03-expressions.md#type-inference)). So editing a body can't change any caller's types, and a signature alone tells you what a function takes and gives.

A function's name is a value, of a type written `fn(Creature) -> str`, so `team.map(status)` passes `status` itself. Arguments are positional. There are no named arguments, no default values and no variadic functions: a function that takes any number of values takes a list, as `average_hp` does. An argument to an `inout` parameter is marked at the call, as in `hit(embercat, inout mossling)`.

### Typed holes

`?` is a **typed hole**: an expression that stands for code you haven't written yet. It takes the type its place expects, and `= ?` makes a whole function body a hole. Each hole gets the warning W0300, *hole*, and the program still runs:

```stilt W0300:6
type Element = | Fire | Water | Plant

fn effectiveness(attacker: Element, defender: Element) -> i64 {
  match (attacker, defender) {
    (Fire, Plant) | (Water, Fire) | (Plant, Water) => 200
    _ => ?
  }
}

fn main() / io { print("{effectiveness(Fire, Plant)}") }
```

```output
200
```

Reaching a hole panics, with the kind `hole`. `stilt build --release` refuses a program that has one ([declarations.running-holes](../../reference/10-declarations.md#declarations.running-holes)). `stilt show main.effectiveness/body` prints what each hole expects: its type, the effects it can perform, the bindings in scope, and functions whose result fits ([The command line](../commands.md#stilt-show)). A hole whose type can't be inferred, as in `let x = ?`, is E0312, *type that can't be inferred*.

## Patterns

A **pattern** describes the shape of a value and binds names to its parts. Patterns appear in `match` and `catch` arms, `let` and `var`, `if let`, `for` loops and closure parameters. These are the forms ([patterns.pattern-forms](../../reference/09-patterns.md#patterns.pattern-forms)):

| Pattern | Matches |
| --- | --- |
| `_` | Anything, and binds nothing |
| `hp` | Anything, and binds it to `hp` |
| `0`, `-1`, `"Embercat"`, `true`, `()` | Equal values. Strings in a pattern can't interpolate |
| `MAX_HP`, `i64.MAX` | Values equal to the constant |
| `(a, b)` | Tuples, element by element |
| `Flee`, `Heal(n)` | That variant, with its payload matched by position |
| `Creature { hp: 0, name, .. }` | Records of that type. `name` binds the field `name`, and `..` skips the fields not listed |
| `[a, b]` | Lists of exactly two elements |
| `[first, ..]`, `[first, ..rest]` | Lists of at least one element. `rest` binds the others as a `List` |
| `p \| q` | Either alternative |

Without `..`, a record pattern lists every field, and leaving one out is E0316, as in a literal. Patterns nest, as in `Creature { element: Fire, .. }` in the chapter's first example. A list pattern matches by length:

```stilt
fn line_up(names: List<str>) -> str {
  match names {
    [] => "nobody"
    [one] => "{one} fights alone"
    [first, second] => "{first} against {second}"
    [first, ..rest] => "{first} against {rest.len()} others"
  }
}

fn main() / io {
  for names in [[], ["Embercat"], ["Embercat", "Mossling"], ["Embercat", "Mossling", "Tidepup"]] {
    print(line_up(names))
  }
}
```

```output
nobody
Embercat fights alone
Embercat against Mossling
Embercat against 2 others
```

A variant in a pattern needs no module. It names a variant of the type being matched, so with `e: arena.Element`, the pattern `Fire` matches `arena.Fire` ([patterns.variants-by-type](../../reference/09-patterns.md#patterns.variants-by-type)). A name that is neither a variant of that type nor anything in scope is E0211, *unknown name*.

A binding holds a copy of the part it matched ([Values and types](02-values.md)). Bindings can't change, except those of a `var` statement, as in `var (a, b) = pair`.

Some values can't be matched by their parts:

- **Floats.** Only `_` and a binding match a float, because NaN is unequal to itself. An integer literal matched against a float, or a constant whose type holds a float, is E0328, *float in a pattern*.
- **Constants with a written `Eq`.** A pattern compares part by part, while `==` calls the type's `eq`. If the program writes an `Eq` for a type, a constant whose type holds it is E0331, *constant with a written `Eq` in a pattern*. Compare it in a guard instead, as in `c if c == CHAMPION` ([patterns.constants-with-written-eq](../../reference/09-patterns.md#patterns.constants-with-written-eq)).

Ranges such as `1..=9`, `@` bindings and patterns after `..`, as in `[.., last]`, are syntax errors, E0100.

## Guards and alternatives

A `match` takes the first arm whose pattern matches. An arm can add a **guard**, `if` and a `bool`, and then matches only when the guard is true. The guard sees the names its pattern binds:

```stilt
fn condition(hp: i64) -> str {
  match hp {
    0 => "fainted"
    n if n < 10 => "weak, {n} HP"
    _ => "ready"
  }
}

fn main() / io { print("{condition(0)}, {condition(4)}, {condition(30)}") }
```

```output
fainted, weak, 4 HP, ready
```

When an arm's pattern has alternatives, its guard is tried with each one that matches, from left to right, so a guard can run more than once ([patterns.guards](../../reference/09-patterns.md#patterns.guards)).

Every alternative binds the same names, with the same types, because the arm's body uses them whichever one matched. An alternative that binds other names than the first is E0217, *alternatives bind different names*:

```stilt E0217:5
type Element = | Fire | Water | Plant

fn burns(pair: (Element, Element)) -> bool {
  match pair {
    (Fire, other) | (_, Fire) => true
    _ => false
  }
}
```

The arms of a `match` have one type. An arm of type `Never`, such as one that returns or panics, fits any type ([patterns.arm-types](../../reference/09-patterns.md#patterns.arm-types)).

## Exhaustiveness

A `match` must cover every value of its type. Variants, `bool`, tuples, records and list lengths can be covered arm by arm. Integers, strings and floats have too many values, so a `match` on them needs a `_` or a binding. A `match` that misses a case is E0329, *patterns that don't cover every value*, and the error names a missing case, here `Plant`:

```stilt E0329:4
type Element = | Fire | Water | Plant

fn weakness(e: Element) -> Element {
  match e {
    Fire => Water
    Water => Plant
  }
}
```

The check doesn't reason about values, so arms with guards or constants cover nothing. This `match` is rejected, although its guards cover every integer:

```stilt E0329:2
fn condition(hp: i64) -> str {
  match hp {
    n if n <= 0 => "fainted"
    n if n < 10 => "weak"
    n if n >= 10 => "ready"
  }
}
```

Replace the last arm with `_ => "ready"` to fix it.

An arm that can never match, because the arms before it cover everything it would, gets the warning W0301, *unreachable arm* ([patterns.unreachable-arms](../../reference/09-patterns.md#patterns.unreachable-arms)):

```stilt W0301:7
type Element = | Fire | Water | Plant

fn label(attacker: Element, defender: Element) -> str {
  match (attacker, defender) {
    (Fire, _) => "fire attacks"
    (_, Fire) => "fire defends"
    (Fire, Fire) => "fire on fire"
    _ => "no fire"
  }
}
```

A type with no values, such as `Never`, needs no arm: `match n {}` covers it ([patterns.types-without-values](../../reference/09-patterns.md#patterns.types-without-values)).

## `let` and let-else

`let` and `var` take a pattern, so `let (attacker, defender) = pair` binds two names. That pattern must be **irrefutable**: its form alone guarantees a match. These patterns are irrefutable:

- `_`, a binding and `()`;
- a tuple or record pattern whose parts are irrefutable;
- the variant of a type with a single variant, such as `CreatureId(n)`, when its payload patterns are irrefutable;
- `[..]` and `[..rest]`;
- an or-pattern with an irrefutable alternative.

Every other pattern is **refutable**. A refutable pattern in `let` or `var` without `else`, a `for` loop or a closure parameter is E0321, *refutable pattern* ([patterns.irrefutable-positions](../../reference/09-patterns.md#patterns.irrefutable-positions)):

```stilt E0321:2
fn leader(team: List<str>) -> str {
  let [first, ..] = team
  first
}
```

A refutable pattern can bind with **let-else**: `let P = e else x`. If `e` matches `P`, the names of `P` are in scope after the statement. Otherwise `x` runs, and it must leave: return, raise, `break`, `continue`, or call a function such as `panic`:

```stilt
fn parse(line: str) -> str {
  let [name, hp] = line.split(",") else return "bad line: {line}"
  let n = hp.to_i64() else return "bad HP: {hp}"
  "{name} has {n} HP"
}

fn main() / io { for line in ["Embercat,30", "Mossling", "Tidepup,lots"] { print(parse(line)) } }
```

```output
Embercat has 30 HP
bad line: Mossling
bad HP: lots
```

The two `else` lines of `parse` look alike and mean different things. `[name, hp]` is refutable, so the first line is a let-else. `n` is irrefutable, so the second means `let n = (hp.to_i64() else return …)`: the `else` fallback of an `Option` ([Expressions](03-expressions.md#the-else-fallback)). In a let-else, an `else` branch that doesn't leave, as in `let [first, ..] = team else ""`, is E0311, *mismatched types* ([patterns.else-after-pattern](../../reference/09-patterns.md#patterns.else-after-pattern)).

To test a refutable pattern without leaving, use `if let P = e { … }` ([Expressions](03-expressions.md#if-let)).

## No type aliases

A `type` declaration declares a record or a variant type, and nothing else. Any other `type X = …` is a syntax error, E0100:

```stilt E0100:1
type Team = List<str>
```

That includes a single variant without its `|`, since `type CreatureId = CreatureId(i64)` reads as an alias. A second name for a type would give it two homes. For a distinct type over another, write a newtype ([Namespaces and newtypes](#namespaces-and-newtypes)).
