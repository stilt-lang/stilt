# Parameter modes

A function can read an argument, or change it where the caller keeps it. Here `status` reads a creature, and `heal` changes one:

```stilt
type Element = | Fire | Water | Plant

type Creature = { name: str, element: Element, hp: i64, attack: i64 }

/// The name and hit points of `c`.
fn status(c: Creature) -> str { "{c.name}: {c.hp} HP" }

/// Gives `c` back `amount` hit points.
fn heal(inout c: Creature, amount: i64) { c.hp += amount }

fn main() / io {
  var mossling = Creature { name: "Mossling", element: Plant, hp: 18, attack: 6 }
  heal(inout mossling, 10)
  print(status(mossling))
}
```

```output
Mossling: 28 HP
```

Each parameter has a **parameter mode**, which says what the function can do with its argument. The parameter `c` of `status` has the mode `let`, the default, which is never written: `status` gets its own copy of the creature, and can only read it. The parameter `c` of `heal` has the mode `inout`: `heal` works on the caller's `mossling`, and the caller sees the change. The call marks the argument `inout` as well, so you can see at the call which variables can change.

| Mode | Parameter | Argument | The callee | The caller |
| --- | --- | --- | --- | --- |
| `let` | `c: Creature` | `status(e)` | Reads its own copy | Keeps its value |
| `inout` | `inout c: Creature` | `heal(inout place, …)` | Reads and changes the caller's place | Sees every change |

A method's receiver has the same two modes, written `self` and `inout self` ([Traits and generics](06-traits.md#self-and-its-modes)), and so does a closure's parameter, as in `|inout c| { c.hp += 1 }` ([Expressions](03-expressions.md#closures)). The mode is part of the function's type: `heal` has the type `fn(inout Creature, i64)` ([declarations.function-types](../../reference/10-declarations.md#declarations.function-types)).

## `let` parameters

A `let` parameter is an independent copy of the argument, so nothing the callee does can change the caller's value ([values.passing-values](../../reference/05-values.md#values.passing-values)). The callee can't modify it either. Assigning to it, to a part of it, or calling an `inout self` method on it is E0403, *modifying what can't be modified*:

```stilt E0403:6
type Element = | Fire | Water | Plant

type Creature = { name: str, element: Element, hp: i64, attack: i64 }

fn rested(c: Creature, full: i64) -> Creature {
  c.hp = full
  c
}
```

To work on a changed copy, bind one with `var`:

```stilt
type Element = | Fire | Water | Plant

type Creature = { name: str, element: Element, hp: i64, attack: i64 }

fn rested(c: Creature, full: i64) -> Creature {
  var c = c
  c.hp = full
  c
}

fn main() / io {
  let tired = Creature { name: "Mossling", element: Plant, hp: 18, attack: 6 }
  let fresh = rested(tired, 34)
  print("{fresh.hp} {tired.hp}")
}
```

```output
34 18
```

`fresh` and `tired` behave as separate values, whatever the compiler does with their memory. It passes `tired` without copying it, and copies the creature's memory only when `rested` writes to it while `tired` still holds it ([how values are stored](../../reference/rationale/05-values.md#value-semantics)). Within one function, `stilt show` marks each write that may copy a value another binding still holds with the `copy` fact ([Copies](05-errors.md#copies)).

## `inout` parameters

An `inout` parameter lets the callee read the caller's place, change any part of it, or assign all of it. When the call ends, the caller's place holds the result.

The argument must be a **place**: a variable followed by fields, tuple fields and indexes, such as `mossling`, `battle.left.hp` or `team[0]`. An entry of a map is a place too. This program counts each creature's wins in a map:

```stilt
fn bump(inout n: i64) { n += 1 }

fn main() / io {
  var wins: Map<str, i64> = Map.with_default(0)
  for winner in ["Embercat", "Tidepup", "Embercat"] { bump(inout wins[winner]) }
  print("{wins}")
}
```

```output
{"Embercat": 2, "Tidepup": 1}
```

For a name that isn't in the map yet, `wins[winner]` reads the default, `0`, and the call writes `1` back, which inserts the name. On a map without a default, reading a missing key panics with the kind `missing-key` ([std.map-element-places](../../reference/17-std.md#std.map-element-places)).

An `inout` argument must have exactly the parameter's type. The receiver of an `inout self` method, such as `team` in `team.push("Tidepup")`, must be a place too, but it isn't marked. Every other argument is unmarked. A missing or extra `inout` is E0400, *`inout` argument marked wrongly*, and an argument that isn't a place, such as a literal, is E0401, *not a place* ([expressions.inout-arguments](../../reference/08-expressions.md#expressions.inout-arguments)):

```stilt E0400:5 E0401:6
fn bump(inout n: i64) { n += 1 }

fn main() {
  var wins = 0
  bump(wins)
  bump(inout 5)
}
```

So a call changes the caller's variables only where it says so: through an argument marked `inout`, or through the receiver of an `inout self` method.

## Changes that a raise keeps

An `inout` argument keeps every change the callee made, when the callee returns and when it raises. Nothing is rolled back ([values.inout-arguments](../../reference/05-values.md#values.inout-arguments)):

```stilt
type Element = | Fire | Water | Plant

type Creature = { name: str, element: Element, hp: i64, attack: i64 }

fn train(inout c: Creature, rounds: i64) / raise<str> {
  for _ in 0..rounds {
    if c.attack == 10 { raise "{c.name} can't get any stronger" }
    c.attack += 1
  }
}

fn main() / io {
  var embercat = Creature { name: "Embercat", element: Fire, hp: 30, attack: 8 }
  try train(inout embercat, 5) catch e => print(e)
  print("attack {embercat.attack}")
}
```

```output
Embercat can't get any stronger
attack 10
```

`train` raised in its third round, and the caller keeps the two points it gained before. Rolling `embercat` back would mean copying every `inout` argument on entry to every function that can raise. A panic ends the program, so nothing sees an `inout` argument after one.

## Evaluation order

A call evaluates its arguments from left to right, the receiver first, and only then starts. An `inout` argument's place is read when the call starts, after every argument, so a change that a later argument makes to it reaches the callee ([values.inout-argument-order](../../reference/05-values.md#values.inout-argument-order)):

```stilt
fn main() / io {
  var team = ["Embercat", "Mossling", "Tidepup"]
  team.push(team.pop() else "nobody")
  print("{team}")
}
```

```output
["Embercat", "Mossling", "Tidepup"]
```

`push` takes `team` as `inout self`. Its argument runs first: `pop` removes `"Tidepup"` and gives it back. Then `push` starts, reads `team` as the two names `pop` left, and appends `"Tidepup"`. When the call returns or raises, each `inout` argument is written back, from left to right.

## Consumed parameters

A function **consumes** a parameter when its body keeps the value. It does so when it returns the value, stores it in another value, rebinds it with `var`, or passes it to a parameter that its callee consumes. The compiler infers which parameters each function consumes. Nothing in the signature says so, and nothing marks the argument at the call ([values.consumed-parameters](../../reference/05-values.md#values.consumed-parameters)).

```stilt
/// The team with `name` added at the front.
fn with_leader(team: List<str>, name: str) -> List<str> {
  var team = team
  team.insert(0, name)
  team
}

fn main() / io {
  var team = ["Mossling", "Tidepup"]
  team = with_leader(team, "Embercat")
  let bench = ["Tidepup"]
  let both = with_leader(bench, "Mossling")
  print("{team} {both} {bench}")
}
```

```output
["Embercat", "Mossling", "Tidepup"] ["Mossling", "Tidepup"] ["Tidepup"]
```

`with_leader` consumes `team`, because it rebinds it with `var`, and only reads `name`. In `team = with_leader(team, "Embercat")`, the call is the caller's last use of the list, so `with_leader` can grow the list in place, with no copy.

Consumption changes nothing that a program can observe. The callee still gets an independent copy, and the caller can keep using the variable it passed, as `bench` shows. The only difference is cost: `bench` is used after the call, so `with_leader` copies the list before it inserts. `stilt show` prints which parameters a function consumes, in the brackets after its signature, beside its other facts:

```text
$ stilt show main.with_leader
module main [core]
/// The team with `name` added at the front.
fn with_leader(team: List<str>, name: str) -> List<str> [consumes team, panic, alloc] {
  var team: List<str> = team // consumes `team`
  team.insert(0, name) // `List.insert` can panic; `List.insert` allocates
  team // `team` escapes, returned
}
```

For `main`, it notes at the second call that `` `bench` is used after this call, so `with_leader` can't reuse it ``.

A function that consumes a parameter still can't modify it directly: that is E0403, as for any `let` parameter. Rebind it with `var` first.

## Inferred modes

Consumption is one of several facts that the compiler infers about each value a function binds, and that `stilt show` prints. Together they are the value's **modes**, one point on each of five axes ([modes.bindings-and-axes](../../reference/13-modes.md#modes.bindings-and-axes)). A parameter's locality is its consumption:

| Axis | Points | The question it answers |
| --- | --- | --- |
| locality | `local`, `escapes` | Does the value leave the function that binds it? |
| uniqueness | `unique`, `shared` | At a write, can another copy of the value still be in use? |
| once | `once`, `many` | Can the closure run more than once? |
| portability | `portable`, `fixed` | Can the value go to another task? |
| contention | `calm`, `contended` | Can several tasks reach the value at once? |

You never write a mode, and none is part of a function's type: `local`, `unique` and `once` are ordinary names. A mode changes nothing that a program means. It records what the compiler chose: where a value lives, where a write happens in place, and what can run in parallel ([modes.fact-not-type](../../reference/13-modes.md#modes.fact-not-type)).

`stilt show` prints a mode only where it isn't the default, at the line that causes it. Two axes show up in everyday code:

```stilt
fn run(f: fn() -> List<str>) -> List<str> { f() }

fn main() / io {
  var team = ["Embercat", "Mossling"]
  let before = team
  team.push("Tidepup")
  let lead = || ["Tidepup"].concat(team)
  print("{run(lead)} {before}")
}
```

```output
["Tidepup", "Embercat", "Mossling", "Tidepup"] ["Embercat", "Mossling"]
```

- `team` is `shared` at the push, because `before` still holds a copy, so the push copies the list before it changes it ([Uniqueness](../../reference/13-modes.md#uniqueness)).
- `lead` is `once`, because `run` calls its parameter `f` once, so `lead` can give its captured `team` up at the call instead of copying it ([Once](../../reference/13-modes.md#once)).

In core, no mode causes an error, and every value is `portable` and `calm`. The advanced tier's `par`, `Shared<T>` and views each demand a mode of the values they take, and an error there names the value and the axis in one line ([Demands](../../reference/13-modes.md#demands)).

## The law of exclusivity

The **law of exclusivity** is what lets `inout` change the caller's value without references: while one part of a function modifies a place, nothing else can touch an overlapping place. An `inout` parameter means copy-in, copy-out: the callee works on the value of the place, and the result is written back when the call ends. A compiler changes the place in memory directly instead. Under the law, no program can tell the two apart.

Two places **overlap** when, after every index is removed from both, one is a prefix of the other ([modes.overlap](../../reference/13-modes.md#modes.overlap)):

| Places | Overlap |
| --- | --- |
| `battle.left` and `battle` | Yes |
| `battle.left` and `battle.left.hp` | Yes |
| `battle.left` and `battle.right` | No |
| `team[0]` and `team[1]` | Yes, whatever the indexes are |

An access to a place is a **modification**, which is an assignment, an `inout` argument or an `inout self` receiver, or else a **read**. An `inout` argument is modified for the whole call. A `let` argument is read while it is evaluated, which ends before the call starts. A `for` loop over a place reads it for the whole of the loop's body. Every other access ends as soon as it is done ([modes.durations](../../reference/13-modes.md#modes.durations)).

The law says that while an access is in progress, no access to an overlapping place can begin if either of the two is a modification. Reads can overlap freely ([modes.law](../../reference/13-modes.md#modes.law)). In practice, this rules out two things, which the next two sections show: passing overlapping places `inout` to one call, and changing what a `for` loop reads.

## Overlapping `inout` arguments

Two `inout` arguments of one call can't overlap, and neither can an `inout` argument and an `inout self` receiver. Two creatures that trade blows can't come from the same list, because `team[0]` and `team[1]` overlap. That is E0402, *overlapping `inout` arguments*, at the later of the two:

```stilt E0402:10
type Element = | Fire | Water | Plant

type Creature = { name: str, element: Element, hp: i64, attack: i64 }

fn trade(inout a: Creature, inout b: Creature) {
  a.hp -= b.attack
  b.hp -= a.attack
}

fn opening(inout team: List<Creature>) { trade(inout team[0], inout team[1]) }
```

The result of such a call would depend on which argument is written back last, so the compiler rejects it. Two different variables, or two different fields, don't overlap. A `let` argument is read before the call starts, so it can name the same place as an `inout` argument:

```stilt
type Element = | Fire | Water | Plant

type Creature = { name: str, element: Element, hp: i64, attack: i64 }

type Battle = { left: Creature, right: Creature }

fn trade(inout a: Creature, inout b: Creature) {
  a.hp -= b.attack
  b.hp -= a.attack
}

fn heal(inout c: Creature, amount: i64) { c.hp += amount }

fn main() / io {
  let embercat = Creature { name: "Embercat", element: Fire, hp: 30, attack: 8 }
  let tidepup = Creature { name: "Tidepup", element: Water, hp: 32, attack: 7 }
  var battle = Battle { left: embercat, right: tidepup }
  trade(inout battle.left, inout battle.right)
  heal(inout battle.left, battle.left.attack)
  print("{battle.left.hp} {battle.right.hp}")
}
```

```output
31 24
```

`battle.left` and `battle.right` are different fields. In the call of `heal`, `battle.left.attack` is read before `heal` starts, so `amount` is `8` throughout. To work on two elements of one list, pass the list once with their indexes, as `trade_at(inout team, 0, 1)`.

## Loops over a place

Inside a `for` loop over a place, a modification of an overlapping place is E0404, *changing a list while reading it*, at the modification. That includes a call that takes the place `inout`, or an `inout self` method on it ([modes.change-while-iterating](../../reference/13-modes.md#modes.change-while-iterating)):

```stilt E0404:8
type Element = | Fire | Water | Plant

type Creature = { name: str, element: Element, hp: i64, attack: i64 }

fn remove(inout team: List<Creature>, name: str) { team.retain(|c| c.name != name) }

fn drop_fainted(inout team: List<Creature>) {
  for c in team { if c.hp == 0 { remove(inout team, c.name) } }
}
```

The loop reads `team`, and `remove` modifies it. If this were allowed, the change would copy the whole list without saying so, and the loop would go on reading the old creatures. The error offers two fixes. The first is `retain`, which keeps the elements that pass a test:

```stilt
type Element = | Fire | Water | Plant

type Creature = { name: str, element: Element, hp: i64, attack: i64 }

fn drop_fainted(inout team: List<Creature>) { team.retain(|c| c.hp > 0) }

fn main() / io {
  var team = [
    Creature { name: "Embercat", element: Fire, hp: 0, attack: 8 },
    Creature { name: "Tidepup", element: Water, hp: 32, attack: 7 },
  ]
  drop_fainted(inout team)
  print("{team.len()} left: {team[0].name}")
}
```

```output
1 left: Tidepup
```

The second is to collect the changes during the loop, in another list, and apply them after it. Reading `team` inside the loop is fine. A loop over a value that isn't a place, such as `team.enumerate(0)`, reads a new list, so its body can change `team`.

## What can be modified

Only `var` bindings and `inout` parameters can be modified. `let` bindings and `let` parameters can't, `self` receivers among them, and neither can the names that a pattern binds outside a `var`. Modifying any of them is E0403, which is reported alone, never with E0402 or E0404 ([modes.what-can-be-modified](../../reference/13-modes.md#modes.what-can-be-modified)).

A closure captures the variables it uses by copy, when it is created, and can't modify them:

```stilt E0403:3
fn main() / io {
  var wins = 0
  let win = || { wins += 1 }
  print("{wins}")
}
```

In JavaScript, `win` would change the outer `wins`. In Stilt it holds a copy, and can't change that copy either. A closure that computes a new value returns it. One that changes the caller's place takes it as an `inout` parameter, as `|inout wins| { wins += 1 }`, and the call passes the place marked `inout`.

[Why Stilt is this way](10-design.md#parameter-modes) gives the reasons for these rules, and what else was considered. Swift's `inout` and its law of exclusivity follow the same idea.
