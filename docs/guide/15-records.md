# Records and variadic generics

A function can return a record without declaring its type first:

```stilt
fn tally(results: List<bool>) -> { won: i64, lost: i64 } {
  var won = 0
  for r in results { if r { won += 1 } }
  { won: won, lost: results.len() - won }
}

fn main() / io {
  let t = tally([true, false, true])
  print("{t.won} won, {t.lost} lost")
  print("{t}")
}
```

```output
2 won, 1 lost
{ lost: 1, won: 2 }
```

`{ won: i64, lost: i64 }` is a record type written where it is used, so a small result needs no `type` declaration. This chapter covers three features of the `advanced` tier: anonymous records, functions over every record with a given field, and functions over tuples of any length. A module that writes them is an advanced module, and one that only calls such a function stays in core ([tiers](08-programs.md#module-headers-tiers-and-limits)).

## Anonymous records

An **anonymous record** is a record whose type has no declaration, as `{ won: 2, lost: 1 }`. Two anonymous record types are the same when they have the same fields with the same types, in any order. So the written order isn't part of the type, and an anonymous record compares, hashes and shows its fields in alphabetical order, as `{ lost: 1, won: 2 }` ([field order](../../reference/07-types.md#records.field-order)).

A `{` followed by a field name and a `:` begins a record literal. So `{ x }` is a block, and `{ x: x }` a record. After the first field, `g` alone is short for `g: g`.

An anonymous record is never a declared record, even when the fields agree. Where a `Creature` is expected, `{ name: "Embercat", element: Fire, hp: 30, attack: 8 }` is E0311, *mismatched types*. An anonymous record type has no home module, so it has no methods and no trait impls of its own ([anonymous records](../../reference/07-types.md#records.no-home)).

## Record bounds

One function can work on every record that has the fields it needs. Here `heal` works on a `Creature` and on a training dummy alike:

```stilt
type Element = | Fire | Water | Plant
type Creature = { name: str, element: Element, hp: i64, attack: i64 }

fn label(x: { name: str, .. }) -> str { "[{x.name}]" }

fn heal<T: { hp: i64, .. }>(inout x: T, amount: i64) { x.hp += amount }

fn renamed<T: { name: str, .. }>(x: T, to: str) -> T { { ..x, name: to } }

fn main() / io {
  var embercat = Creature { name: "Embercat", element: Fire, hp: 30, attack: 8 }
  var dummy = { name: "Straw dummy", hp: 50 }
  heal(inout embercat, 5)
  heal(inout dummy, 5)
  print("{label(embercat)} {embercat.hp}, {label(dummy)} {dummy.hp}")
  print("{renamed(embercat, "Blaze")}")
}
```

```output
[Embercat] 35, [Straw dummy] 55
Creature { name: "Blaze", element: Fire, hp: 35, attack: 8 }
```

A **record bound**, such as `T: { hp: i64, .. }`, names fields the way a trait bound names methods. Any record with a field `hp` of type `i64` meets it, declared or anonymous, and the body reads and writes that field. The `..` says the type can have other fields too, and a bound without it is E0341.

`label` writes the bound in the parameter's type instead. An **open record type**, `{ name: str, .. }`, stands for a type parameter with no name. It can only be a parameter's type, because the type it stands for comes from the caller: as a result, a field or a local's type, it is E0341 ([open parameter types](../../reference/07-types.md#records.open-parameter-types)).

A type that lacks a field the bound names, or whose field has another type, is E0318, *unsatisfied bound*, and the message names the field ([record bounds](../../reference/07-types.md#records.record-bounds)).

## Record update

`{ ..x, name: to }` is an **update**: a copy of `x` with the fields written replaced. An update never adds or removes a field, so its type is the type of `x`, and `renamed` gives back a `Creature` when it gets one.

This form is for an anonymous record or a type parameter with a record bound. For a declared record, name the type, as `Creature { ..embercat, hp: 0 }`, which is core ([update](../../reference/07-types.md#records.update)).

## Variadic generics

A variadic function takes a tuple of any length. This `zip` pairs up the lists of a roster, however many there are:

```stilt
fn zip<..Ts>(lists: (..List<Ts>)) -> List<(..Ts)> {
  let n = [..lists.len()].min() else 0
  var out: List<(..Ts)> = []
  for i in 0..n { out.push((..lists[i])) }
  out
}

fn apply<..Ts, R>(f: fn(..Ts) -> R, args: (..Ts)) -> R { f(..args) }

fn main() / io {
  print("{zip((["Embercat", "Mossling"], [30, 34]))}")
  print("{zip((["Embercat", "Mossling"], [30, 34], [8, 6]))}")
  print("{apply(|hp, damage| hp - damage, (30, 16))}")
}
```

```output
[("Embercat", 30), ("Mossling", 34)]
[("Embercat", 30, 8), ("Mossling", 34, 6)]
14
```

A **pack**, `..Ts` among the generics, is a type parameter that stands for zero or more types. You write it **spread**, with `..`, inside a tuple type or a function type's parameters. `(..List<Ts>)` is a tuple with one list for each type of the pack, so at `Ts = (str, i64)` it is `(List<str>, List<i64>)` ([type spreads](../../reference/07-types.md#variadics.type-spreads)).

A value whose type spreads a pack, like `lists`, is a **pack tuple**. Its length isn't known in the body, so a pattern, `.0`, `for` or an index on it is E0342. You map over it instead, with a spread expression ([spread expressions](../../reference/07-types.md#variadics.spread-expressions)):

| Expression | Builds |
| --- | --- |
| `(..e)` | A tuple of `e` for each element, as `(..lists[i])` does |
| `[..e]` | A list of the same results, as `[..lists.len()]` does |
| `f(..e)` | A call that passes the results as arguments, as `f(..args)` does |

In each one, `e` is evaluated once for each element, in order, and every pack tuple named in `e` stands for that element. A spread that names no pack, or names two different packs, is E0343.

A function always takes a fixed number of arguments ([functions](04-declarations.md#functions)), so a variadic function takes its values as one tuple: `zip((a, b, c))`, with `()` for an empty pack. A pack goes among a function's generics or last among a type's parameters; anywhere else it is E0344 ([packs](../../reference/07-types.md#variadics.packs)). A pack can take bounds, as in `..Ts: Show`, and then a pack tuple can be shown or compared whole.
