# Traits and generics

Here is a trait for things that deal damage, and a generic function that works on any of them:

```stilt
type Element = | Fire | Water | Plant

type Creature = { name: str, element: Element, hp: i64, attack: i64 }

type Move = { name: str, element: Element, power: i64 }

/// Something that deals damage.
trait Damaging {
  fn damage(self) -> i64
}

impl Damaging for Creature {
  fn damage(self) -> i64 { self.attack }
}

impl Damaging for Move {
  fn damage(self) -> i64 { self.power }
}

fn total<T: Damaging>(xs: List<T>) -> i64 { xs.fold(0, |sum, x| sum + x.damage()) }

fn main() / io {
  let embercat = Creature { name: "Embercat", element: Fire, hp: 30, attack: 8 }
  let tidepup = Creature { name: "Tidepup", element: Water, hp: 32, attack: 7 }
  let snare = Move { name: "Root Snare", element: Plant, power: 30 }
  let jet = Move { name: "Bubble Jet", element: Water, power: 35 }
  print("{total([embercat, tidepup])} {total([snare, jet])}")
}
```

```output
15 65
```

A **trait** declares methods, here `damage`, and an **impl** implements them for one type. `total` is **generic**: `T` stands for any type, and the **bound** `T: Damaging` limits it to the types that implement `Damaging`, so the body can call `x.damage()`.

## Generic functions

A function is generic when it declares type parameters in angle brackets after its name. A type parameter is an uppercase name, and it stands for the same type everywhere in the signature:

```stilt
fn first_or<T>(xs: List<T>, fallback: T) -> T { xs.first() else fallback }

fn main() / io {
  print(first_or(["Embercat", "Mossling"], "nobody"))
  print("{first_or([], 0)}")
}
```

```output
Embercat
0
```

A call never names its type arguments: inference finds them from the arguments and from the type the context expects. The first call makes `T` a `str`, and the second makes it an `i64`, the default type of an integer literal. Where nothing fixes a type, annotate a binding, as in `let names: List<str> = []` ([types.no-type-arguments](../../reference/07-types.md#types.no-type-arguments)).

A type that a body leaves undecided is E0312, *type that can't be inferred*, at the expression that introduced it:

```stilt E0312:1
fn main() { let fighters = [] }
```

Nothing says what the list holds. `let fighters: List<str> = []` fixes it.

Lowercase names among a function's generics are effect-row variables ([Errors and effects](05-errors.md#row-variables)).

## Bounds

A bound follows a type parameter, with `+` between several traits, as in `<T: Ord>` or `<K: Eq + Hash>`. Inside the function, the bounds are all that is known about `T`: they give its values their traits' methods, and the operators those traits stand behind:

```stilt
fn largest<T: Ord>(xs: List<T>) -> Option<T> {
  var best = xs.first() else return None
  for x in xs { if x > best { best = x } }
  Some(best)
}

fn main() / io {
  let nobody: List<str> = []
  print("{largest([30, 34, 32])} {largest(["Embercat", "Tidepup"])} {largest(nobody)}")
}
```

```output
Some(34) Some("Tidepup") None
```

Without its bound, `largest` couldn't compare `x` with `best`. An operator or an interpolation that needs a trait the bounds don't give is E0318, *unsatisfied bound*. A method that no bound gives is E0314, *no such method or member*:

```stilt E0318:1
fn same<T>(a: T, b: T) -> bool { a == b }
```

A call whose types don't meet the bounds gets E0318 too, at the call. Maps have no order ([Structural impls](#structural-impls)), so this call is rejected:

```stilt E0318:5
fn smaller<T: Ord>(a: T, b: T) -> T { if a < b { a } else { b } }

fn main() {
  let wins: Map<str, i64> = Map.new()
  let _ = smaller(wins, wins)
}
```

A body reports each missing trait of each type once, at its first use ([traits.bound-reported-once](../../reference/11-traits.md#traits.bound-reported-once)).

Bounds go on the generics of functions and `impl` blocks, and nowhere else. A bound on a type's parameter, as in `type Ranked<T: Ord>`, is a syntax error, E0100, and so is a trait that requires another, as in `trait Sorted: Ord` ([traits.bounds](../../reference/11-traits.md#traits.bounds)).

## Traits

A trait's methods are signatures, and each can have a **default** body. Inside a trait, `Self` is the type that implements it. `impl Trait for Type { … }` implements the trait for a type:

```stilt
type Element = | Fire | Water | Plant

type Creature = { name: str, element: Element, hp: i64, attack: i64 }

type Move = { name: str, element: Element, power: i64 }

trait Damaging {
  fn damage(self) -> i64
  fn summary(self) -> str { "deals {self.damage()} damage" }
}

impl Damaging for Creature {
  fn damage(self) -> i64 { self.attack }
  fn summary(self) -> str { "{self.name} hits for {self.attack}" }
}

impl Damaging for Move {
  fn damage(self) -> i64 { self.power }
}

fn report<T: Damaging>(x: T) / io { print(x.summary()) }

fn main() / io {
  report(Creature { name: "Embercat", element: Fire, hp: 30, attack: 8 })
  report(Move { name: "Bubble Jet", element: Water, power: 35 })
}
```

```output
Embercat hits for 8
deals 35 damage
```

An impl holds a method for each method of the trait that has no default. It can leave out the others, as the impl for `Move` leaves out `summary`, and then the default applies. It holds no other method. Each method has the trait's signature, with `Self` replaced by the impl's type: the same parameter modes and types, the same return type and the same effect row ([traits.impl-signatures](../../reference/11-traits.md#traits.impl-signatures)). In core, every function of a trait is a method, whose first parameter is `self` or `inout self`.

Each of these impls breaks one of those rules:

```stilt E0305:9 E0306:10 E0307:14
type Element = | Fire | Water | Plant

type Creature = { name: str, element: Element, hp: i64, attack: i64 }

type Move = { name: str, element: Element, power: i64 }

trait Damaging { fn damage(self) -> i64 }

impl Damaging for Creature {
  fn defense(self) -> i64 { self.hp }
}

impl Damaging for Move {
  fn damage(inout self) -> i64 { self.power }
}
```

The impl for `Creature` lacks `damage`, which has no default: E0305, *missing trait member*. `defense` isn't a method of `Damaging`: E0306, *member not in the trait*. The impl for `Move` takes `inout self` where the trait takes `self`: E0307, *method signature differs from the trait's*.

An impl applies to a whole type constructor, such as every `List<T>`, and its generics can carry bounds. An impl for `List<i64>` alone is E0302, *invalid impl type*. A program can implement its own traits for the built-in types:

```stilt
trait Describe {
  fn describe(self) -> str
}

impl<T: Show> Describe for List<T> {
  fn describe(self) -> str { "{self.len()} entries: {self}" }
}

impl Describe for i64 {
  fn describe(self) -> str { "{self} HP" }
}

fn main() / io { print("{["Embercat", "Mossling"].describe()}, {30.describe()}") }
```

```output
2 entries: ["Embercat", "Mossling"], 30 HP
```

`impl<T: Show> Describe for List<T>` implements `Describe` for every list whose elements can be shown. The methods of a trait impl take no `pub`: they are visible wherever both the trait and the type are.

A core trait abstracts over `Self` alone. Traits with parameters of their own, functions without `self` and constants belong to the advanced tier ([Trait parameters and constructor traits](13-trait-parameters.md)). Core has no operator traits, since the arithmetic operators work only on numbers, and a trait can't be used as a type (E0212, *wrong kind of name*).

## Coherence and the orphan rule

Two rules make each impl unique, and say where it lives:

- **Coherence.** A trait has at most one impl for each type constructor. A second one is E0304, *overlapping impls*.
- **The orphan rule.** An impl lives in the trait's module or in the type's module. Anywhere else it is E0303, *orphan impl*.

```stilt E0303:1
impl Hash for f64 {
  fn hash(self) -> u64 { 0 }
}
```

`Hash` and `f64` both live in `std.prelude`, so no other module can connect them, and floats are never map keys ([Floats](#floats)).

Together, the rules give each trait and type constructor at most one impl in the whole program, in one of two modules, so every method call has one meaning. Because an impl covers a whole constructor, an impl for `List<str>` can't sit beside one for every `List<T>` ([traits.coherence](../../reference/11-traits.md#traits.coherence)).

## Inherent methods

A type's own functions and constants live in an `impl` block that names no trait, in the module that declares the type:

```stilt
type Element = | Fire | Water | Plant

type Creature = { name: str, element: Element, hp: i64, attack: i64 }

type Team = { members: List<Creature> }

impl Team {
  const MAX_SIZE: i64 = 6
  fn new() -> Self { Self { members: [] } }
  fn add(inout self, c: Creature) { self.members.push(c) }
  fn total_hp(self) -> i64 { self.members.fold(0, |sum, c| sum + c.hp) }
}

fn main() / io {
  var team = Team.new()
  team.add(Creature { name: "Embercat", element: Fire, hp: 30, attack: 8 })
  team.add(Creature { name: "Tidepup", element: Water, hp: 32, attack: 7 })
  print("{team.total_hp()} HP, room for {Team.MAX_SIZE - team.members.len()} more")
}
```

```output
62 HP, room for 4 more
```

An `impl` block holds three kinds of member, and in it `Self` is the block's type:

- a **method** has `self` as its first parameter, and is called as `team.add(…)`;
- an **associated function** has no `self`, and is called as `Team.new()`;
- a **constant** is read as `Team.MAX_SIZE`, as `f64.PI` is.

An inherent `impl` in any other module is E0301, *inherent impl outside the type's module*. The built-in types live in `std.prelude`, so a program adds methods to `List` or `str` only through a trait of its own. A name is defined once across all the inherent blocks of a type (E0208), and the block's functions and constants are private to the module unless marked `pub` ([Programs](08-programs.md)).

For a generic type such as `type Stack<T> = { items: List<T> }`, the block is written `impl<T> Stack<T>`, naming each parameter once. It can bound them, as `impl<T: Ord> Stack<T>` does, and its functions then exist only for those types. The prelude gives `sort` and `sorted` only to lists of `Ord` elements, so calling one on any other list is E0318, *unsatisfied bound*:

```stilt E0318:3
fn main() {
  let wins: Map<str, i64> = Map.new()
  let _ = [wins].sorted()
}
```

A constant has one value for all of a block's type arguments, so `Stack.LIMIT` takes none, and its type can't name `T` or `Self` ([declarations.impl-constants](../../reference/10-declarations.md#declarations.impl-constants)).

## `self` and its modes

A method's receiver is written `self` or `inout self`, with no type, because its type is always `Self`. The mode means what it means for any parameter ([Parameter modes](07-modes.md)):

- with `self`, the method gets an independent copy of the receiver, and can't change it;
- with `inout self`, the method changes the caller's place. The call doesn't write `inout`: `team.add(c)` changes `team`.

Only a `var` binding or an `inout` parameter can change, so an `inout self` method on a `let` binding is E0403, *modifying what can't be modified*:

```stilt E0403:11
type Element = | Fire | Water | Plant

type Creature = { name: str, element: Element, hp: i64, attack: i64 }

impl Creature {
  fn heal(inout self, amount: i64) { self.hp += amount }
}

fn main() {
  let mossling = Creature { name: "Mossling", element: Plant, hp: 20, attack: 6 }
  mossling.heal(5)
}
```

Making `mossling` a `var` fixes it. The receiver of `inout self` must be a place, so `Team.new().add(c)` is E0401, *not a place*. The receiver is changed for the whole call, as an `inout` argument is, so the law of exclusivity applies to it ([Parameter modes](07-modes.md#the-law-of-exclusivity)). A method that wants to change its own copy rebinds it first, as in `var t = self` ([Consumed parameters](07-modes.md#consumed-parameters)).

`self` exists only in methods, and `Self` only in `impl` and trait blocks. Anywhere else, each is E0215, *`self` or `Self` where it doesn't exist*.

## Method resolution

A method call `x.m(…)` finds `m` from the type of `x` alone. That type must be known where the call stands, from the code before it, or the call is E0312, which asks for an annotation. Its outermost constructor is enough: after `var names = []`, the call `names.push("Embercat")` is valid and decides the element type ([types.known-types](../../reference/07-types.md#types.known-types)).

With `C` the constructor of the receiver's type, such as `List` for a `List<str>`, these are tried in order:

1. An inherent function `m` of `C`. If it takes no `self`, the call is E0314, *no such method or member*.
2. A method `m` of a trait that `C` implements and that is in scope: declared in the prelude, in this module, or in a module that a `use` names ([traits.traits-in-scope](../../reference/11-traits.md#traits.traits-in-scope)). If the receiver's type arguments don't meet the impl's bounds, the call is E0318.
3. For a type parameter, the methods of the traits in its bounds.
4. A field `m` of a record, or an element of a tuple, that holds a function. The call calls that function.

If none finds `m`, the call is E0314. Each step appears here:

```stilt
trait Fighter {
  fn title(self) -> str
}

type Trainer = { name: str, cheer: fn(str) -> str }

impl Trainer {
  fn enter(self) -> str { "{self.name} enters the arena" }
}

impl Fighter for Trainer {
  fn title(self) -> str { "Trainer {self.name}" }
}

fn main() / io {
  let ana = Trainer { name: "Ana", cheer: |who| "Go, {who}!" }
  print(ana.enter())
  print(ana.title())
  print(ana.cheer("Embercat"))
}
```

```output
Ana enters the arena
Trainer Ana
Go, Embercat!
```

`ana.enter()` stops at step 1, `ana.title()` at step 2, and `ana.cheer("Embercat")` at step 4.

When methods of two traits match, the call is E0319, *ambiguous method*. Name the trait with a [qualified call](#qualified-calls) instead:

```stilt E0319:17
trait Fighter { fn title(self) -> str }

trait Ranked { fn title(self) -> str }

type Trainer = { name: str, wins: i64 }

impl Fighter for Trainer {
  fn title(self) -> str { "Trainer {self.name}" }
}

impl Ranked for Trainer {
  fn title(self) -> str { "{self.name}, {self.wins} wins" }
}

fn main() / io {
  let ana = Trainer { name: "Ana", wins: 3 }
  print(ana.title())
  print(Ranked.title(ana))
}
```

An inherent method can't share its name with a method of a trait that the type implements, including the traits records get without an impl ([Structural impls](#structural-impls)). That is E0308, *inherent method hides a trait method*, so a record can't have an inherent `show`:

```stilt E0308:6
type Element = | Fire | Water | Plant

type Creature = { name: str, element: Element, hp: i64, attack: i64 }

impl Creature {
  fn show(self) -> str { "{self.name} ({self.hp} HP)" }
}
```

Implement `Show` for `Creature` instead ([Showing values](#showing-values)).

Resolution never looks at the arguments' types, and each method has one home for each type, so Stilt has no overloading ([traits.no-overloading](../../reference/11-traits.md#traits.no-overloading)).

## Qualified calls

`Type.m(x, …)` and `Trait.m(x, …)` call a method with its receiver as the first argument. `Type.m` finds `m` as steps 1 and 2 of resolution do. An `inout self` receiver is then an ordinary `inout` argument, marked at the call. Both forms are also function values, which can be passed to `map`:

```stilt
type Element = | Fire | Water | Plant

type Creature = { name: str, element: Element, hp: i64, attack: i64 }

impl Creature {
  fn heal(inout self, amount: i64) { self.hp += amount }
  fn label(self) -> str { "{self.name}: {self.hp} HP" }
}

fn main() / io {
  var mossling = Creature { name: "Mossling", element: Plant, hp: 20, attack: 6 }
  mossling.heal(4)
  Creature.heal(inout mossling, 10)
  print(Creature.label(mossling))
  print("{[mossling].map(Creature.label)} {[30, 34].map(Show.show)} {Ord.compare(30, 34)}")
}
```

```output
Mossling: 34 HP
["Mossling: 34 HP"] ["30", "34"] Less
```

`Show.show` passed to `map` over a `List<i64>` is a `fn(i64) -> str`: its type is fixed where it is used, as a generic function's is ([traits.qualified-calls](../../reference/11-traits.md#traits.qualified-calls)).

## The prelude traits

The prelude declares four traits, which operators, maps and interpolation use:

| Trait | Methods | Used by |
| --- | --- | --- |
| `Eq` | `fn eq(self, other: Self) -> bool` | `==` and `!=` |
| `Ord` | `fn compare(self, other: Self) -> Ordering` | `<`, `<=`, `>` and `>=` |
| `Hash` | `fn hash(self) -> u64` | Map keys, which need `Eq + Hash` |
| `Show` | `fn show(self) -> str`, and `fn show_nested(self) -> str`, whose default is `self.show()` | Interpolation |

`a == b` means `Eq.eq(a, b)`, and `a != b` is its negation. `a < b` means `Ord.compare(a, b) == Less`, and the other comparisons work the same way. On the numeric types the operators are built in, but a type parameter is never a numeric type, so in generic code they always go through `compare` ([Floats](#floats)):

```stilt
fn clamp<T: Ord>(x: T, lo: T, hi: T) -> T { if x < lo { lo } else if x > hi { hi } else { x } }

fn main() / io {
  print("{clamp(120, 0, 99)} {clamp("Tidepup", "Embercat", "Mossling")}")
  print("{clamp((30, "Embercat"), (30, "Mossling"), (34, "Mossling"))}")
}
```

```output
99 Mossling
(30, "Mossling")
```

The value `hash` returns is unspecified, except that equal values have equal hashes within one run. A type whose `Eq` the program writes gets no automatic `Hash`, and can't be a map key until the program writes that impl too. Equal values must then have equal hashes ([traits.hash-follows-written-eq](../../reference/11-traits.md#traits.hash-follows-written-eq)).

## Structural impls

Tuples, records, variant types, `List`, `Option` and `Result` implement all four prelude traits without an impl, as long as each of their components does. So `Option<T>` implements `Eq` when `T` does. These **structural impls** go through the components from first to last:

- **Equality** compares components with `eq`, and stops at the first pair that differs.
- **Order** compares components with `compare` until a pair differs. A record compares its fields in the order they are declared. A variant type orders its variants as declared, then compares payloads, so `None < Some(0)` and `Fire < Plant`.
- **Hashing** hashes every component.

```stilt
type Element = | Fire | Water | Plant

type Entry = { wins: i64, name: str }

fn main() / io {
  let embercat = Entry { wins: 3, name: "Embercat" }
  let mossling = Entry { wins: 1, name: "Mossling" }
  let tidepup = Entry { wins: 3, name: "Tidepup" }
  print("{embercat == mossling} {Fire < Plant} {mossling < embercat}")
  print("{[tidepup, mossling, embercat].sorted()}")
}
```

```output
false true true
[Entry { wins: 1, name: "Mossling" }, Entry { wins: 3, name: "Embercat" }, Entry { wins: 3, name: "Tidepup" }]
```

`Entry` puts `wins` first, so entries sort by wins, then by name. An impl the program writes in the type's module replaces the structural one ([Showing values](#showing-values)).

The integer types, `bool`, `str` and `()` implement all four traits, and `f32` and `f64` all but `Hash`. `str` is ordered by its bytes, and `false < true`. Function types implement none, so a function can't be compared, shown or used as a key ([traits.built-in-impls](../../reference/11-traits.md#traits.built-in-impls)).

`Map` implements `Eq` and `Show`, but not `Ord` or `Hash`, and its `Eq` needs the key type's `Hash`. Two maps are equal when they hold the same entries, in any order, and a map's default takes no part:

```stilt
fn main() / io {
  var a = Map.new()
  a["Embercat"] = 3
  a["Mossling"] = 1
  var b = Map.with_default(0)
  b["Mossling"] = 1
  b["Embercat"] = 3
  print("{a == b} {a} {b}")
}
```

```output
true {"Embercat": 3, "Mossling": 1} {"Mossling": 1, "Embercat": 3}
```

## Showing values

`Show` has two methods because a string shows differently on its own and inside another value. For `str`, `show` returns the text as it is, and `show_nested` returns it quoted. Interpolation calls `show`, and containers call `show_nested` on their elements. Every other built-in and structural impl shows a value the same way in both places:

```stilt
type Element = | Fire | Water | Plant

type Creature = { name: str, element: Element, hp: i64, attack: i64 }

impl Show for Creature {
  fn show(self) -> str { "{self.name} ({self.hp} HP)" }
}

fn main() / io {
  let name = "Embercat"
  print("{name} {[name]} {name.show_nested()}")
  let embercat = Creature { name, element: Fire, hp: 30, attack: 8 }
  print("{embercat} {[embercat]} {Some(embercat)}")
}
```

```output
Embercat ["Embercat"] "Embercat"
Embercat (30 HP) [Embercat (30 HP)] Some(Embercat (30 HP))
```

The impl for `Creature` replaces the structural one. It keeps the default `show_nested`, which calls `show`, so a creature looks the same inside a list. With one method, `["a, b"]` and `["a", "b"]` would look alike. [How values show](09-library.md#how-values-show) gives the output of every type.

## Floats

Floats have two orders. The operators `==` and `<` on floats follow IEEE 754: NaN is unequal to everything, itself included, and `-0.0 == 0.0`. `Eq.eq` agrees with `==`. `Ord.compare` is a total order instead:

- `-0.0` is less than `0.0`, as in the IEEE 754 totalOrder;
- every NaN equals every other NaN, and is greater than every other value, `inf` included.

Everything that goes through `compare` uses the total order: sorting, comparing compound values, and `<` in generic code. So sorting by a float is always total and deterministic:

```stilt
fn larger<T: Ord>(a: T, b: T) -> T { if a < b { b } else { a } }

fn main() / io {
  let nan = f64.NAN
  let zero = 0.0
  print("{nan == nan} {-0.0 == zero} {-0.0 < zero} {1.0 < nan}")
  print("{Ord.compare(nan, nan)} {Ord.compare(-0.0, zero)} {larger(1.0, nan)}")
  print("{[nan] == [nan]} {(-0.0,) < (zero,)} {[nan] < [1.0]} {[nan] <= [nan]}")
  print("{[2.0, nan, zero, -0.0, -1.0].sorted()}")
}
```

```output
false true false false
Equal Less nan
false true false true
[-1.0, -0.0, 0.0, 2.0, nan]
```

`1.0 < nan` is false under IEEE 754. Inside `larger`, `T` is a type parameter, so `<` means `compare`, and NaN is the largest value. A list compares its elements with `eq`, so `[nan] == [nan]` is false, while `[nan] <= [nan]` goes through `compare` and is true ([traits.floats](../../reference/11-traits.md#traits.floats)).

Floats don't implement `Hash`, so they can't be map keys:

```stilt E0318:1
fn main() { let by_power: Map<f64, str> = Map.new() }
```
