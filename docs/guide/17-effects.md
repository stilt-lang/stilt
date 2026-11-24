# Effects, tasks and parallelism

A battle rolls dice, and a test of the battle needs to know what the dice say. An effect lets the test choose the rolls:

```stilt pass:26
use std.random

type Element = | Fire | Water | Plant
type Creature = { name: str, element: Element, hp: i64, attack: i64 }

effect Dice {
  fn roll(sides: i64) -> i64
}

/// The damage of one hit: the attack of `attacker` plus a roll of a six-sided die.
fn damage(attacker: Creature) -> i64 / Dice {
  attacker.attack + Dice.roll(6)
}

fn main() / io {
  let fair = handler Dice {
    fn roll(sides: i64) -> i64 {
      var rng = random.Rng.from_entropy()
      rng.below(sides) + 1
    }
  }
  let embercat = Creature { name: "Embercat", element: Fire, hp: 30, attack: 8 }
  with fair { print("Embercat hits for {damage(embercat)}.") }
}

test "a hit adds the roll to the attack" {
  let threes = handler Dice { fn roll(sides: i64) -> i64 { 3 } }
  let embercat = Creature { name: "Embercat", element: Fire, hp: 30, attack: 8 }
  with threes { assert damage(embercat) == 11 }
}
```

`damage` asks for a roll with `Dice.roll(6)`, and doesn't say how the roll is made. `main` answers with random numbers, and the test answers with a fixed `3`, so its result is always `11`. Nothing passes the dice from `main` down to `damage`: the `/ Dice` in its signature says it needs them, as `/ io` says a function prints.

Effects, tasks and shared values belong to the `advanced` tier, and the parallel loops of `std.par` to core. A module that declares or performs an effect, writes a handler or a `with`, or names `std.task` or `std.sync` is an advanced module ([tiers](08-programs.md#module-headers-tiers-and-limits)).

## Effects and handlers

An **effect** declares **operations**: function signatures with no body, such as `fn roll(sides: i64) -> i64`. `Dice.roll(6)` **performs** the operation: it asks the nearest handler of `Dice` for the answer. A **handler**, `handler Dice { … }`, implements every operation of the effect, and `with h { … }` installs the handler `h` while its block runs, at any depth of calls ([handlers](../../reference/12-effects.md#handlers.with)).

An effect sits in a row beside `io` and `raise<E>`, and passes through functions as they do. Here the closure given to `fold` performs both effects, inside `total_damage`:

```stilt
type Element = | Fire | Water | Plant
type Creature = { name: str, element: Element, hp: i64, attack: i64 }

effect Dice {
  fn roll(sides: i64) -> i64
}

effect Log {
  fn log(msg: str)
}

fn total_damage(team: List<Creature>) -> i64 / {Dice, Log} {
  team.fold(0, |sum, c| {
    let d = c.attack + Dice.roll(6)
    Log.log("{c.name} deals {d}")
    sum + d
  })
}

fn main() / io {
  let threes = handler Dice { fn roll(sides: i64) -> i64 { 3 } }
  let printed = handler Log { fn log(msg: str) { print("log: {msg}") } }
  let team = [
    Creature { name: "Embercat", element: Fire, hp: 30, attack: 8 },
    Creature { name: "Mossling", element: Plant, hp: 34, attack: 6 },
  ]
  with threes, printed { print("total {total_damage(team)}") }
}
```

```output
log: Embercat deals 11
log: Mossling deals 9
total 20
```

`with threes, printed` installs both handlers. Performing an effect in a function whose row doesn't hold it is E0502, as for `io`. `main`, tests and doc examples can't hold a declared effect in their row: every performance must run under a `with`, or it is E0512, *effect that reaches `main`*.

The rules for declaring them are short:

- An effect has at least one operation (E0518). It can take type parameters, as `effect Ask<T> { fn ask() -> T }`, and a row holds at most one instance of each effect (E0515).
- A handler implements each operation once, with the types the effect declares. A missing operation, an extra one or one with other types is E0511.
- A handler is a value, of type `handler Dice`. It captures the bindings it names by copy, as a closure does, and it can be stored, passed and returned.
- A handler installed inside another of the same effect hides it. A handler's own operations perform their effect on the handler outside it.

## Handlers that take control

A handler written `handler Name -> R` **takes control** of each performance. `resume(v)` goes on from the performance with `v` as its value, and gives back what the rest of the `with` block ends with, of type `R`. An operation that doesn't resume ends the whole `with` with its own value. This handler refuses a die with no sides:

```stilt
effect Dice {
  fn roll(sides: i64) -> i64
}

fn main() / io {
  let checked = handler Dice -> str {
    fn roll(sides: i64) -> i64 {
      if sides < 1 { "no die has {sides} sides" } else { resume(sides) }
    }
  }
  print(with checked { "rolled {Dice.roll(6)}" })
  print(with checked { "rolled {Dice.roll(0)}" })
}
```

```output
rolled 6
no die has 0 sides
```

For `Dice.roll(6)`, the handler resumes with `6`, so the block goes on and its string is the `with`'s value. For `Dice.roll(0)`, it doesn't resume, and its message is the value instead. If the rest of the block raises, or jumps out of the `with`, the `with` ends that way, and the handler's code after its `resume` never runs ([resuming](../../reference/12-effects.md#handlers.resuming)).

An operation that doesn't resume ends every call between the performance and the `with`, as a raise does: the code after the performance never runs, and an `inout` argument keeps what the call wrote before it ([calls that a handler ends](../../reference/12-effects.md#handlers.call-that-handler-ends)). A few rules keep `resume` simple:

- A handler resumes at most once on each path. A `resume` in a loop, in a closure or after another `resume` is E0514.
- `resume` outside an operation of a `-> R` handler is E0513.
- An operation takes its arguments by value, so an `inout` parameter is E0517. An operation that changes a value takes it and returns the new one, as `hp = Heal.heal(hp)`.
- A `with` handles every performance of its effect that reaches it, as a `catch` handles every raise. So a call of a function value inside a `with` must pair that value's row with the effect, as for `raise<E>` ([pairing](../../reference/12-effects.md#handlers.with-pairing)); otherwise it is E0516.

## Tasks

A **task** is a function that runs alongside the code that started it. `std.task` starts and waits for tasks, and both perform the effect `async`. `main` picks its handler, `task.threads()` or `task.sequential()`, and the code that starts tasks is the same under both:

```stilt
use std.task

fn total_hp(team: List<i64>) -> i64 { team.fold(0, |sum, hp| sum + hp) }

fn both(a: List<i64>, b: List<i64>) -> (i64, i64) / async {
  let x = task.spawn(|| total_hp(a))
  let y = task.spawn(|| total_hp(b))
  (x.await(), y.await())
}

fn main() / io {
  with task.threads() {
    print("start")
    let t = task.spawn(|| print("in a task"))
    print("{both([30, 34], [32])}")
    t.await()
  }
}
```

```output
start
in a task
(64, 32)
```

`task.spawn(f)` runs `f` as a task and gives its handle, and `t.await()` waits for the task's value.

A program means what it does when each task runs to its end as soon as it starts. That is `task.sequential()`, the handler of a program that installs none. Under `task.threads()`, tasks run at the same time, and what they print still appears where the sequential run prints it. So `in a task` comes before `(64, 32)` above, whichever thread finishes first ([the sequential run](../../reference/14-tasks.md#tasks.same-output-under-every-handler)). Files, the network and the clock are the exception to this order: tasks reach them at the same time, in no fixed order.

A task's function captures values by copy, so a task shares no place with the code that started it. It can print and start tasks, but it can't raise: a task that can fail returns a `Result`, or runs in a scope (below). It performs no other effect either (E0502). A `with` of a task handler ends once every task started under it has ended ([task functions](../../reference/14-tasks.md#tasks.task-functions)).

## Shared state

Tasks share no place, so a value that several tasks change lives in a `Shared<T>` of `std.sync`. A `Shared<T>` is a **handle**: a copy of it reaches the same value. You reach the value only inside `when`:

```stilt
use std.sync
use std.task

type Element = | Fire | Water | Plant
type Creature = { name: str, element: Element, hp: i64, attack: i64 }

/// Moves `n` HP from `source` to `target`.
fn drain(source: sync.Shared<Creature>, target: sync.Shared<Creature>, n: i64) {
  when source, target {
    source.hp -= n
    target.hp += n
  }
}

fn main() / io {
  let mossling = sync.Shared.new(Creature { name: "Mossling", element: Plant, hp: 34, attack: 6 })
  let tidepup = sync.Shared.new(Creature { name: "Tidepup", element: Water, hp: 32, attack: 7 })
  with task.threads() {
    task.spawn(|| drain(mossling, tidepup, 10))
    task.spawn(|| drain(tidepup, mossling, 4))
  }
  when mossling, tidepup { print("{mossling.name} {mossling.hp}, {tidepup.name} {tidepup.hp}") }
}
```

```output
Mossling 28, Tidepup 38
```

`when source, target { … }` waits until it holds both values, runs its block with each name standing for its value, and then lets them go. Because one `when` holds all its values at once, no two tasks can wait on each other. The `when` blocks that reach one value run in the order the sequential run gives them, so the program prints the same under threads ([`when`](../../reference/14-tasks.md#shared.when-order)).

These rules keep `when` safe:

- A `when` inside another, or a call inside a `when` of a function that runs one, is E0430. A function that runs a `when` has the fact `locks`, which `stilt show` prints and `without locks` forbids.
- A value put in a `Shared<T>`, and anything a task captures, must be safe on another thread: a view is E0432.
- A view of a value that a `when` holds lasts only inside its block, which lets the value go when it ends: a `when` whose value views a name it holds, or a view of one assigned to a variable from outside, is E0422 ([views.escaping](../../reference/13-modes.md#views.escaping)).
- Two names of one `when` whose values have the same type can be one value, so the law of exclusivity treats them as one name. `swap(inout source.hp, inout target.hp)` is E0402, as it would be with one name ([names that can be one place](../../reference/14-tasks.md#shared.names-that-may-be-one-place)). Uniqueness reads them the same way: after `let old = source.log`, a push to `target.log` copies while `old` lasts, which `without copy` forbids ([when's names](../../reference/13-modes.md#modes.shared-when-names)).
- A `when` reached through a function value or a handler, on a value that a `when` around it already holds, panics with the kind `deadlock`, since under threads it would wait for itself.

Handles can hold one another, so values linked through `Shared<T>` can form a **cycle**: a value that reaches itself. Here each creature names the other as its rival:

```stilt
use std.sync

type Fighter = { name: str, rival: Option<sync.Shared<Fighter>> }

fn main() / io {
  let embercat = sync.Shared.new(Fighter { name: "Embercat", rival: None })
  let mossling = sync.Shared.new(Fighter { name: "Mossling", rival: Some(embercat) })
  when embercat { embercat.rival = Some(mossling) }
  when mossling { print(mossling.name) }
}
```

```output
Mossling
```

A cycle is freed once nothing else reaches it, as any value is. Freeing runs none of your code, so when it happens changes nothing a program prints ([cycles](../../reference/14-tasks.md#cycles.freeing)). `stilt show main.Fighter` writes ``// can form a cycle, through `rival` `` after the type.

Tasks that can fail run in a **scope**. `try task.scope(|s| …)` gives a scope `s`, and `try s.spawn(f)` starts a task that can raise. The scope raises the first failure in the sequential order, then cancels its later tasks, and nothing they would print appears ([scopes](../../reference/14-tasks.md#tasks.scope-failure)). A scope ends when `task.scope` returns, so `s` can only start tasks or go to a parameter of type `task.Scope<E>`. Kept anywhere else, even captured by a task, it is E0434.

## Parallel loops

`std.par` runs work on every core with no handler. Here `par.map` works out, for each matchup, how many hits the attacker needs to win, to check that the creatures are balanced:

```stilt
use std.par

type Element = | Fire | Water | Plant
type Creature = { name: str, element: Element, hp: i64, attack: i64 }

fn effectiveness(attacker: Element, defender: Element) -> i64 {
  match (attacker, defender) {
    (Fire, Plant) | (Water, Fire) | (Plant, Water) => 200
    (Fire, Water) | (Water, Plant) | (Plant, Fire) => 50
    _ => 100
  }
}

/// How many hits `a` needs to make `b` faint.
fn hits_to_win(a: Creature, b: Creature) -> i64 {
  let damage = a.attack * effectiveness(a.element, b.element) / 100
  (b.hp + damage - 1) / damage
}

fn main() / io {
  let embercat = Creature { name: "Embercat", element: Fire, hp: 30, attack: 8 }
  let mossling = Creature { name: "Mossling", element: Plant, hp: 34, attack: 6 }
  let tidepup = Creature { name: "Tidepup", element: Water, hp: 32, attack: 7 }
  let matchups = [(embercat, mossling), (mossling, tidepup), (tidepup, embercat)]
  print("{par.map(matchups, |m| hits_to_win(m.0, m.1))}")
  print("{par.both(|| hits_to_win(embercat, mossling), || hits_to_win(mossling, embercat))}")
  var team = [embercat, mossling, tidepup]
  par.each(inout team, |inout c| { c.hp += 10 })
  print("{team.map(|c| c.hp)}")
  print(par.fold(["a", "b", "c", "d"], "", |p, q| "({p}{q})"))
}
```

```output
[3, 3, 3]
(3, 10)
[40, 44, 42]
((ab)(cd))
```

The module has four functions ([parallel calls](../../reference/14-tasks.md#par.std-par)):

| Call | Gives |
| --- | --- |
| `par.map(xs, f)` | The list of `f` of each element |
| `par.each(inout xs, f)` | Nothing: `f` changes each element of `xs` in place |
| `par.both(f, g)` | The pair of the values of `f` and `g` |
| `par.fold(xs, empty, f)` | The elements combined by `f`, or `empty` for an empty list |

The closures you give them perform no effect, so the result is the same as running them one after another, on any number of threads. A closure that prints or raises is E0502, and one that reaches a `Shared<T>` or a view is E0431. When several calls panic, the program reports the first in order. `std.par` is part of the core library, so naming it keeps a module in its tier.

`fold` combines the elements in a balanced tree that depends only on the list's length, as the last line shows. So a sum of floats has the same bits on every machine ([fold](../../reference/14-tasks.md#par.fold-tree)). The compiler runs these calls on a thread for each core, or on as many as the environment variable `STILT_THREADS` names, such as `STILT_THREADS=1`.
