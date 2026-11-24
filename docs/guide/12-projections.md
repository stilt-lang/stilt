# Projections and writing through views

A **projection** is a function that gives its caller a place to change, instead of a value. This team hands out one creature's HP, and puts it back to zero if a hit takes it below:

```stilt
type Team = { names: List<str>, hp: List<i64> }

impl Team {
  /// The HP of member `i`. It never stays below zero.
  fn hp_of(inout self, i: i64) -> inout i64 {
    yield self.hp[i]
    if self.hp[i] < 0 { self.hp[i] = 0 }
  }
}

fn main() / io {
  var team = Team { names: ["Embercat", "Mossling"], hp: [30, 34] }
  team.hp_of(1) -= 16
  print("{team.names[1]} has {team.hp_of(1)} HP.")
  team.hp_of(1) -= 40
  print("{team.names[1]} has {team.hp_of(1)} HP.")
}
```

```output
Mossling has 18 HP.
Mossling has 0 HP.
```

The result type `inout i64` makes `hp_of` a projection. Its body doesn't return a number: it **yields** the place `self.hp[i]`, and `team.hp_of(1) -= 16` changes that place inside `team`. Once the caller is done, `hp_of` resumes after the `yield` and runs its last line. A function that returned a copy could do neither.

The second half of the chapter covers **writable views**: views of part of a list that write to the list, so you can change part of it without copying it out and back. Projections and writable views are in the `advanced` tier.

## Calling a projection

A call of a projection is a **place**, like `team.hp[1]`. You can assign to it, use `+=` or `-=` on it, pass it `inout`, call an `inout self` method on it, and follow it with `.field`, `.0` or `[i]`. Anywhere else, the call is read: the value is copied out, and the projection resumes before the copy is used. So `"{team.hp_of(1)}"` above prints a copy ([projections.call-is-place](../../reference/13-modes.md#projections.call-is-place)).

A projection can only be called. It has no function type, so `let f = Team.hp_of` is E0426.

## Yielding once

Every path through a projection's body must run `yield` exactly once. If a path ends without one, the caller would have no place to use:

```stilt E0424:5
fn hp_at(inout hp: List<i64>, i: i64) -> inout i64 {
  if i < hp.len() {
    yield hp[i]
  }
}

fn main() / io {
  var hp = [30, 34]
  hp_at(inout hp, 0) = 20
  print("{hp}")
}
```

The `if` has no `else`, so one path reaches the end of the body without a `yield`, which is E0424. A second `yield` on one path, and a `yield` inside a loop, are E0424 too. The arms of an `if` or a `match` count one by one, and an arm that panics needs no `yield`, so `else { panic("no creature at {i}") }` fixes the program ([projections.once-on-every-path](../../reference/13-modes.md#projections.once-on-every-path)).

`yield` takes a place rooted in `self`, another `inout` parameter or a `var` of the body. A `yield` anywhere but a projection's body, such as in a closure or a test, is E0425 ([projections.yield](../../reference/13-modes.md#projections.yield)).

## When a projection runs

A projection holds its `inout` arguments for as long as the caller uses the place it yields. The call starts where that use starts: at the store of an assignment, or at the start of the enclosing call for an `inout` argument. Under the law of exclusivity, two calls that both hold `team` can't be the two `inout` arguments of one call ([Overlapping `inout` arguments](07-modes.md#overlapping-inout-arguments)):

```stilt E0402:17
type Team = { names: List<str>, hp: List<i64> }

impl Team {
  fn hp_of(inout self, i: i64) -> inout i64 {
    yield self.hp[i]
  }
}

fn swap(inout a: i64, inout b: i64) {
  let t = a
  a = b
  b = t
}

fn main() / io {
  var team = Team { names: ["Embercat", "Mossling"], hp: [30, 34] }
  swap(inout team.hp_of(0), inout team.hp_of(1))
  print("{team.hp}")
}
```

Projections on two different values are fine. They start from left to right and resume from right to left, as nested calls do ([projections.when-projection-runs](../../reference/13-modes.md#projections.when-projection-runs)).

What the caller does with the place runs in the caller, so its effects are the caller's. If the caller raises meanwhile, the projection doesn't resume: the code after its `yield` doesn't run, and its `inout` arguments keep the changes made before the `yield` ([projections.raising-during-access](../../reference/13-modes.md#projections.raising-during-access)). A projection can't raise itself: `raise<E>` in its row is E0427. If it can fail, make it panic, or have its caller check first.

## Writable views

A view that you make through `inout` **writes** its source: a change through the view changes the list. `view.into(inout xs, start, end)` makes one. Bound by `var`, it is a **writable binding**, and `v[i]` is a place that writes `xs[start + i]`. `view.part(inout v, start, end)` takes a writable part of one. `view.split(inout xs, at, f)` calls `f` once with the two parts of `xs`, each writable:

```stilt
use std.view

/// Puts every HP in `v` back to `full`.
fn heal(inout v: view.View<List<i64>>, full: i64) {
  for i in 0..v.len() { v[i] = full }
}

fn main() / io {
  var hp = [0, 12, 5, 30]
  {
    var front = view.into(inout hp, 0, 2)
    heal(inout front, 30)
    front[1] -= 4
  }
  view.split(inout hp, 2, |inout a, inout b| {
    a[0] -= 5
    b[0] += 5
  })
  print("{hp}")
}
```

```output
[25, 26, 10, 30]
```

`front` writes `hp`, and `stilt show` says so at the binding: `` `front` writes `hp` ``. `split` gives you two parts of one list to change at once, which two `inout` arguments of the same list can't be. Views of strings are read-only. `into` and `split` count as allocating, because they make the list's storage unique where it was shared; `part` doesn't ([projections.writable-views](../../reference/13-modes.md#projections.writable-views)).

Three rules follow from what a view writes:

- **A `var` view must write every source it has.** `var v = View.of(hp, 0, 1)` is E0428, because that view only reads `hp`. Make it with `view.into(inout hp, …)`, or bind it with `let` to read ([projections.writable-bindings](../../reference/13-modes.md#projections.writable-bindings)).
- **Nothing else reaches the source while a writable binding lives.** Reading `hp`, changing it, looping over it and viewing it are E0429 until the binding's scope ends. That is why `front` sits in a block above.
- **A writable binding is a source of its own.** `let w = front.view(0, 1)` reads `front`, not `hp`, so `front[0] = 1` while `w` lives is E0423, as it would be for a list ([projections.places-through-views](../../reference/13-modes.md#projections.places-through-views)).

Here the program reads `hp` while `front` still writes it:

```stilt E0429:7
use std.view

fn main() / io {
  var hp = [30, 34, 32]
  var front = view.into(inout hp, 0, 2)
  front[0] = 20
  print("{hp.len()}")
}
```

## Views that write across calls

A function's result views every argument it could view, and writes each one passed `inout`. So a function that takes `inout hp` can return a writable view of it, which the caller binds with `var`. A projection can yield a writable view as well:

```stilt
use std.view

/// The first half of `hp`, to write through.
fn front(inout hp: List<i64>) -> view.View<List<i64>> {
  view.into(inout hp, 0, hp.len() / 2)
}

/// The second half of `hp`, as a place.
fn back(inout hp: List<i64>) -> inout view.View<List<i64>> {
  yield view.into(inout hp, hp.len() / 2, hp.len())
}

fn heal(inout v: view.View<List<i64>>, full: i64) {
  for i in 0..v.len() { v[i] = full }
}

fn main() / io {
  var hp = [0, 12, 5, 30]
  {
    var f = front(inout hp)
    f[0] = 9
  }
  heal(inout back(inout hp), 32)
  print("{hp}")
}
```

```output
[9, 12, 32, 32]
```

A function whose result reads an `inout` parameter is E0428, because the result must write it: make the view with `view.into`. If a result also views a `let` argument, as `f(inout hp, names)` would, the caller can only bind it with `let`, since the result reads `names` ([projections.results-that-write](../../reference/13-modes.md#projections.results-that-write)).
