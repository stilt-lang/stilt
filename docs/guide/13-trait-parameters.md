# Trait parameters and constructor traits

A core trait says what a type can do. A **trait parameter** also lets it say what the type holds. Here `Collection<Item>` covers a roster, which holds names, and a list, which holds whatever it holds:

```stilt
trait Collection<Item> {
  fn at(self, i: i64) -> Option<Item>
  fn size(self) -> i64
}

type Roster = { names: List<str> }

impl Collection<str> for Roster {
  fn at(self, i: i64) -> Option<str> { self.names.get(i) }
  fn size(self) -> i64 { self.names.len() }
}

impl<T> Collection<T> for List<T> {
  fn at(self, i: i64) -> Option<T> { self.get(i) }
  fn size(self) -> i64 { self.len() }
}

/// The sum of every element of `c`.
fn total<C: Collection<i64>>(c: C) -> i64 {
  var sum = 0
  for i in 0..c.size() {
    if let Some(x) = c.at(i) { sum += x }
  }
  sum
}

fn main() / io {
  let roster = Roster { names: ["Embercat", "Mossling", "Tidepup"] }
  print("{roster.size()} creatures, {total([30, 34, 32])} HP in all")
}
```

```output
3 creatures, 96 HP in all
```

`Item` is a type that each impl chooses: `Roster` chooses `str`, and `List<T>` chooses `T`. The bound `C: Collection<i64>` accepts any type whose impl chooses `i64`, so `total` takes a list of HP and refuses a roster.

The chapter also covers trait functions that need no value to call them on, and **constructor traits**, which cover `List` and `Option` alike. A module that declares, implements or bounds such a trait, or writes a member type or a `where` clause, is in the `advanced` tier; one that only calls their methods stays in core ([traits.advanced-tier](../../reference/11-traits.md#traits.advanced-tier)).

## Trait parameters

Each impl gives the trait's parameters their arguments, which can name the impl's own type parameters, as `impl<T> Collection<T> for List<T>` does. A trait still has at most one impl for each type ([Coherence and the orphan rule](06-traits.md#coherence-and-the-orphan-rule)), so the type decides the arguments: implementing both `Convert<f64>` and `Convert<str>` for `i64` is E0304 ([traits.trait-arguments](../../reference/11-traits.md#traits.trait-arguments)).

A bound gives the trait all its arguments, as `C: Collection<i64>`, or none, as `C: Collection`. Some but not all is E0300. A type meets the bound when its impl gives the bound's arguments, so `total(roster)` is E0318, *unsatisfied bound* ([traits.bound-arguments](../../reference/11-traits.md#traits.bound-arguments)).

## Member types and `where`

If a bound leaves a trait parameter open, the function can still name it. Under `C: Collection`, `C.Item` is a **member type**: the type that the impl for `C` chooses for `Item`. A `where` clause after the signature puts a bound on a member type:

```stilt
trait Collection<Item> {
  fn at(self, i: i64) -> Option<Item>
  fn size(self) -> i64
}

impl<T> Collection<T> for List<T> {
  fn at(self, i: i64) -> Option<T> { self.get(i) }
  fn size(self) -> i64 { self.len() }
}

/// The largest element of `c`.
fn largest<C: Collection>(c: C) -> Option<C.Item> where C.Item: Ord {
  var best = c.at(0)
  for i in 1..c.size() {
    if let Some(x) = c.at(i) {
      if let Some(b) = best {
        if x > b { best = Some(x) }
      }
    }
  }
  best
}

fn main() / io { print("{largest([30, 34, 32])} {largest(["Mossling", "Tidepup"])}") }
```

```output
Some(34) Some("Tidepup")
```

`largest` works on a list of HP and on a list of names, because each impl decides what `C.Item` is. A trait parameter does the job of an associated type in Rust, with no `type Item = T` in the impl ([traits.member-types](../../reference/11-traits.md#traits.member-types)). Three mistakes have codes of their own:

- `X.Item` where `X` isn't a type parameter, or where no bound of `X` has a parameter `Item`, is E0334.
- If two bounds of `X` both have an `Item`, `X.Item` is E0335: name it with a generic, as in `C: Collection<T>`.
- A `where` bound on a plain type parameter belongs beside it, so `fn f<T>(x: T) where T: Show` is E0336. So is a `where` clause on a trait's function, because its impls must keep the trait's signature ([traits.where](../../reference/11-traits.md#traits.where)).

## Functions and constants without `self`

A method needs a value to call it on, and sometimes there is none yet: adding up a list of hits starts from zero damage. A trait can declare functions that take no `self`, and constants, each with a default or not:

```stilt
trait Combine {
  fn zero() -> Self
  fn combine(self, other: Self) -> Self
  const NAME: str
}

type Damage = { points: i64 }

impl Combine for Damage {
  fn zero() -> Damage { Damage { points: 0 } }
  fn combine(self, other: Damage) -> Damage { Damage { points: self.points + other.points } }
  const NAME: str = "damage"
}

/// Every element of `xs`, combined into one.
fn combine_all<T: Combine>(xs: List<T>) -> T {
  var acc = T.zero()
  for x in xs { acc = acc.combine(x) }
  acc
}

fn main() / io {
  let total = combine_all([Damage { points: 16 }, Damage { points: 3 }])
  print("{Damage.NAME}: {total.points}")
}
```

```output
damage: 19
```

You name such a function or constant on a type: `T.zero()` on a type parameter bounded by the trait, `Damage.NAME` on a type that implements it, and `Self.zero()` inside the trait. `Combine.zero()` is E0330, because it doesn't say which impl you mean, and the compiler never guesses one from the type the call is expected to have ([traits.functions-without-self](../../reference/11-traits.md#traits.functions-without-self)).

## Constructor traits

`List` and `Option` are **type constructors**: each takes a type argument and makes a type, such as `List<i64>`. A **constructor trait** covers type constructors. It writes `Self` with type arguments, as `Self<A>`:

```stilt
type Odd = | Odd(i64)

trait Mappable {
  fn transform<A, B>(self: Self<A>, f: fn(A) -> B) -> Self<B>
}

impl Mappable for Option {
  fn transform<A, B>(self: Option<A>, f: fn(A) -> B) -> Option<B> {
    match self {
      Some(x) => Some(f(x))
      None => None
    }
  }
}

impl Mappable for List {
  fn transform<A, B>(self: List<A>, f: fn(A) -> B) -> List<B> {
    var out: List<B> = []
    for x in self { out.push(f(x)) }
    out
  }
}

/// Half of `hp`, which must be even.
fn halve(hp: i64) -> i64 / raise<Odd> {
  if hp % 2 == 0 { hp / 2 } else { raise Odd(hp) }
}

fn halved<F: Mappable>(hp: F<i64>) -> F<i64> / raise<Odd> { try hp.transform(halve) }

fn main() / io {
  let one = try halved(Some(30)) catch Odd(n) => None
  let all = try halved([30, 33]) catch Odd(n) => [n]
  print("{one} {all}")
}
```

```output
Some(15) [33]
```

Three things differ from an ordinary trait:

- Each method writes its receiver's type, as `self: Self<A>`, and each impl writes it with its constructor, as `self: Option<A>`. A missing receiver type, in the trait or in an impl, a receiver type in the trait that isn't `Self` with arguments, or a written one anywhere else, is E0338 ([traits.receiver-types](../../reference/11-traits.md#traits.receiver-types)).
- An impl names the bare constructor: `impl Mappable for Option`, not `Option<T>`.
- A generic it bounds takes arguments: under `F: Mappable`, `F<i64>` is a type, and `halved(Some(30))` takes `F` to be `Option`. Alone, it names the functions without `self` and the constants of its bounds, as a type parameter does: were `N` a constant of `Mappable`, `F.N` in `halved(Some(30))` would be the `N` of `impl Mappable for Option`.

The number of type arguments must agree everywhere. `Self` alone in `Mappable`, an impl for `Map`, which takes two, an impl for `List<i64>`, `F` without its argument, and a bound such as `F: Mappable + Show` that mixes a constructor trait with an ordinary one are E0337, *type of the wrong kind* ([traits.constructor-parameters](../../reference/11-traits.md#traits.constructor-parameters)).

`halved` raises what `halve` raises, because `f` passes its argument's effects through ([Effects that pass through](05-errors.md#effects-that-pass-through)). `std` declares no constructor trait: `List` and `Option` have their own `map`.
