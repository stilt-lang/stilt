# Views and iterators

A **view** reads part of a string or a list without copying it. This program views the first two names of a roster:

```stilt
use std.view

fn main() / io {
  let roster = ["Embercat", "Mossling", "Tidepup"]
  let front = view.View.of(roster, 0, 2)
  print("{front} holds {front.len()} names, and the second is {front[1]}.")
}
```

```output
["Embercat", "Mossling"] holds 2 names, and the second is Mossling.
```

`roster.slice(0, 2)` would build a new list and copy two names into it. `View.of(roster, 0, 2)` builds nothing: `front` reads elements 0 and 1 of `roster` where they are. The value a view reads is its **source**, here `roster`. The type of `front` is `View<List<str>>`, written `view.View<List<str>>` after `use std.view`.

The same module has **iterators**: sequences that read from lists, views and maps one element at a time. A module that names `View` or `Iter` is in the `advanced` tier ([Module headers, tiers and limits](08-programs.md#module-headers-tiers-and-limits)).

## Making a view

`View.of(source, start, end)` views the part of `source` between two offsets, counted as `slice` counts them: elements of a list, bytes of a string. `View.all(source)` views the whole, and `v.view(start, end)` views part of a view, with offsets from its own start. An offset out of range panics, as it does for `slice` ([views.making-view](../../reference/13-modes.md#views.making-view)).

This program views the second word of a move's name, and reads past the end of a roster:

```stilt
use std.view

fn main() / io {
  let name = "Flame Pounce"
  let second = view.View.all(name).view(6, 12)
  print("{second} {second.len()} {second.copy() == "Pounce"}")
  let roster = ["Embercat", "Mossling"]
  print("{view.get(view.View.all(roster), 5)}")
}
```

```output
Pounce 6 true
None
```

A view has the length of its part, shows as its part shows, and equals a view of an equal part. To compare a view with a `str`, `copy` it first. `copy` gives the part as a value of its own, and is the only method of a view that allocates.

`len`, `view` and `copy` are methods of every view. `view.get` for list views and `view.chars` for string views are functions of the module ([views.functions-of-views](../../reference/13-modes.md#views.functions-of-views)). A `for` loop goes through a view of a list. Only strings and lists can be viewed: `View<i64>` is E0420.

## What a view can't do

A view reads a value that something else owns, so the compiler keeps two rules. It works out what each view reads by itself.

**A view can't be stored.** A view can be a local, a parameter, a function's result, a closure's capture or the payload of an `Option`. A view in a record field, a variant's payload, a list, a map or a tuple is E0421, and so is `collect` on an iterator of views ([views.view-types](../../reference/13-modes.md#views.view-types)):

```stilt E0421:3 E0421:8
use std.view

type Team = { names: view.View<List<str>> }

fn main() / io {
  let roster = ["Embercat", "Mossling"]
  let front = view.View.all(roster)
  let fronts = [front]
  print("{fronts.len()}")
}
```

**A view can't outlive its source.** A view leaves a function only as its result, and only when each of its sources is a parameter: the caller's argument lives on after the call, so the view does too. Returning a view of a local, giving a block a value that views the block's own binding, or a `when` one that views a name it holds, and capturing a view in a closure that escapes are E0422 ([views.escaping](../../reference/13-modes.md#views.escaping)):

```stilt E0422:5
use std.view

fn starters() -> view.View<List<str>> {
  let roster = ["Embercat", "Mossling", "Tidepup"]
  view.View.of(roster, 0, 2)
}

fn main() / io { print("{starters()}") }
```

`roster` is gone once `starters` returns. The function builds the list itself, so return a copy: `roster.slice(0, 2)`.

## Views across calls

A call's result of a view type views every argument that could be viewed: a string, a list or a view. The compiler reads this from the signature, which says nothing more:

```stilt
use std.view

/// The first word of `name`.
fn first_word(name: str) -> view.View<str> {
  view.View.of(name, 0, name.find(" ") else name.len())
}

fn main() / io {
  let name = "Bubble Jet"
  let word = first_word(name)
  print("{word} {word.len()}")
}
```

```output
Bubble 6
```

`word` views `name`, the one argument `first_word` could view. If two parameters could be viewed, as in `fn pick(a: str, b: str) -> View<str>`, the result views both, and the caller can't change either argument while the result lives ([views.across-calls](../../reference/13-modes.md#views.across-calls)).

## How long a view reads

A view binding reads its sources for its whole scope, as `for x in xs` reads `xs` for its body ([The law of exclusivity](07-modes.md#the-law-of-exclusivity)). A view that no binding holds, as in `View.all(xs).len()`, reads until the end of its statement. The read starts where the source is evaluated, so a later argument of the same call can't change the source either, as in `View.of(xs, 0, grow(inout xs))`. Changing a source while a view reads it is E0423:

```stilt E0423:6
use std.view

fn main() / io {
  var roster = ["Embercat", "Mossling"]
  let front = view.View.of(roster, 0, 1)
  roster.push("Tidepup")
  print("{front}")
}
```

To fix it, push before you take the view, or put the view in a block that ends before the push. The scope is what counts, not the last use: a change after the view's last use but inside its scope is still E0423 ([views.reads-that-last](../../reference/13-modes.md#views.reads-that-last)). A change to a place that doesn't overlap the source, such as another field of the same record, is allowed ([places and accesses](../../reference/13-modes.md#modes.overlap)).

## Iterators

A chain of list methods builds a whole list at each step. An iterator builds none: it hands its elements on one at a time.

```stilt
use std.view

fn main() / io {
  let roster = ["Embercat", "Mossling", "Tidepup"]
  let long = view.Iter.of(roster).filter(|n| n.len() > 7)
  print("{long.collect()} {long.count()}")
  let evens = view.range(0, 100).filter(|x| x % 2 == 0)
  print("{evens.take(3).collect()} {evens.map(|x| x * x).find(|x| x > 50)}")
  for entry in view.Iter.of(roster).enumerate(1) { print("{entry.0}. {entry.1}") }
}
```

```output
["Embercat", "Mossling"] 2
[0, 2, 4] Some(64)
1. Embercat
2. Mossling
3. Tidepup
```

`Iter.of` makes an iterator from a list, `Iter.of_view` from a view of a list, `view.of_map` from a map, in insertion order, and `view.range(start, end)` from the integers from `start` up to `end`. An **adapter** makes a new iterator from one: `map`, `filter`, `take`, `skip`, `take_while`, `skip_while`, `enumerate`, `zip` and `chain`. A **consumer** reads the elements: a `for` loop, `collect`, `fold`, `count`, `any`, `all`, `find`, `first`, `last`, `nth`, `max` and `min` ([iterators](../../reference/13-modes.md#iterators)).

An iterator lives on the heap, so making one, adapting it, consuming it and looping over it allocate, while a `for` over a view allocates nothing ([natives that allocate](../../reference/15-facts.md#facts.native-allocation)). Nothing runs when you make or adapt an iterator. A consumer asks for one element at a time, and each element passes through the adapters in order. So `take(3)` never asks `filter` for a fourth element, and the hundred integers are never in a list. Each consumer starts again from the first element: `long` is read twice above ([views.laziness](../../reference/13-modes.md#views.laziness)).

An adapter calls its closure later, whenever a consumer asks. So the closure can't print or raise (E0502), and can't capture a view (E0422): capture what you need from the view, such as its length. A consumer calls its closure at once, so its effects pass through to the caller ([Effects that pass through](05-errors.md#effects-that-pass-through)). A step that must raise goes in a consumer such as `fold`, or in the list methods.

An iterator reads its sources as a view does, so changing a source while it lives is E0423. An iterator can't be shown or compared (E0318): `collect` it first ([views.iterator-traits](../../reference/13-modes.md#views.iterator-traits)).
