# Polymorphic arguments and lazy values

A **polymorphic function type** lets an argument stay generic, so the function that receives it can call it at more than one type. Here `card` shows a creature's name, a `str`, and its HP, an `i64`, through the same `f`:

```stilt
/// A line about a creature, with each part shown by `f`.
fn card(f: fn<T: Show>(T) -> str, name: str, hp: i64) -> str { "{f(name)} {f(hp)}" }

fn bracketed<T: Show>(x: T) -> str { "[{x}]" }

fn main() / io {
  print(card(bracketed, "Embercat", 30))
  print(card(|x| "<{x}>", "Mossling", 34))
}
```

```output
[Embercat] [30]
<Mossling> <34>
```

A generic function is **instantiated** where it is named: each of its type parameters is fixed there to one type ([Traits and generics](06-traits.md)). With a parameter `f: fn(T) -> str`, `card` would get `bracketed` at one `T`, and `f(name)` and `f(hp)` couldn't both type-check. `fn<T: Show>(T) -> str` declares its own `T`, so each call of `f` instantiates it again: at `str`, then at `i64`.

The chapter also covers polymorphic recursion, which core already has, and `Lazy<T>`, a value computed the first time it is used. A module that writes a polymorphic function type or names `Lazy` is in the `advanced` tier ([Module headers, tiers and limits](08-programs.md#module-headers-tiers-and-limits)).

## Polymorphic function types

A function type declares its type parameters, with their bounds, after `fn`. Where `fn<T: Show>(T) -> str` is expected, you can give one of three things ([polymorphism.arguments](../../reference/07-types.md#polymorphism.arguments)):

- a generic function, named as a value, such as `bracketed`;
- a closure literal, such as `|x| "<{x}>"`, whose `x` it can use only through `Show`;
- a value of the same polymorphic type, such as a parameter passed on.

A function fixed to one type, such as an `fn(i64) -> str`, is E0311, *mismatched types*: it can't take every `T`. A closure that uses `x` beyond its bounds, as `x < x` does, and a generic function that needs a bound the type doesn't give, such as `T: Ord`, are E0318, *unsatisfied bound*.

`f` passes its argument's effects through, as a function parameter that doesn't escape does: if `f` raises, so does `card` ([Effects that pass through](05-errors.md#effects-that-pass-through)). A record field can hold a polymorphic function too, so a record of functions can carry generic behaviour:

```stilt
type Banner = { wrap: fn<T: Show>(T) -> str }

fn announce(b: Banner) -> str { "{b.wrap("Tidepup")} enters with {b.wrap(32)} HP" }

fn main() / io { print(announce(Banner { wrap: |x| "*{x}*" })) }
```

```output
*Tidepup* enters with *32* HP
```

A polymorphic function type can be the type of a parameter, a record field or a variant's payload, and nowhere else. As a type argument, as in `List<fn<T>(T) -> T>`, a function's result or a local's annotation, it is E0340 ([polymorphism.placement](../../reference/07-types.md#polymorphism.placement)). A type parameter that neither its parameters nor its result use is E0339.

## Polymorphic recursion

In **polymorphic recursion**, which is part of core, a generic function calls itself at a different type. Here `depth` at `Nested<T>` calls itself at `Nested<List<T>>`:

```stilt
type Nested<T> = | Flat(T) | Nest(Nested<List<T>>)

/// How many times `n` nests.
fn depth<T>(n: Nested<T>) -> i64 {
  match n {
    Flat(_) => 0
    Nest(inner) => 1 + depth(inner)
  }
}

fn main() / io {
  let hp: Nested<i64> = Nest(Nest(Flat([[30, 34]])))
  print("{depth(hp)}")
}
```

```output
2
```

The compiler checks the call against the written signature, as it checks any call ([polymorphism.recursion](../../reference/07-types.md#polymorphism.recursion)). Such a function reaches types without end, so the compiler can't build a copy of it for each type. It passes each type's methods at run time instead, and the release build's performance report lists the function ([the rationale](../../reference/rationale/07-types.md#polymorphic-recursion)).

## Lazy values

`std.lazy` declares `Lazy<T>`: a value computed by a function the first time `get` asks for it, and kept from then on. Use it for a table that a program needs many times, or not at all:

```stilt
use std.lazy

type Arena = { strong_hits: lazy.Lazy<List<i64>> }

/// The damage of a hit at 200% for each attack from 1 to 99.
fn strong_hits() -> List<i64> {
  var out: List<i64> = []
  for attack in 1..100 { out.push(attack * 200 / 100) }
  out
}

fn main() / io {
  let arena = Arena { strong_hits: lazy.Lazy.new(strong_hits) }
  let copy = arena
  print("{arena.strong_hits.get().len()} {copy.strong_hits.get()[7]}")
}
```

```output
99 16
```

The first `get` builds the table. `copy` shares it, so its `get` builds nothing.

The function given to `new` does nothing a program could see, so no program can tell when it runs, or whether it ran. Its row is empty: a function that prints or raises is E0502. One that runs a `when`, or calls a function that does, is E0435, since it could wait for the code that asked for the value ([polymorphism.lazy-waits-for-nothing](../../reference/07-types.md#polymorphism.lazy-waits-for-nothing)).

A `Lazy` can't be compared or shown: `==` and `"{l}"` are E0318, because they would compute the value unseen. `get` might not end, so a function under `without div` can't call it. The function's own panics and allocations count where you write it, as any closure's do ([polymorphism.lazy-implicit-effects](../../reference/07-types.md#polymorphism.lazy-implicit-effects)).
