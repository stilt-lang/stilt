# Rationale: The value model

Stilt has value semantics and no garbage collector. That leaves these questions, which need precise answers:

- what copying a value costs;
- what `str` is;
- what passing a value does to the caller's variable;
- what an `inout` argument holds after the callee raises;
- in which order expressions are evaluated.

The answers decide what the reference interpreter must model, and what the compiler is free to do instead.

## Value semantics

Every core value behaves as an independent copy, and only a `var` binding or an `inout` parameter can appear to change ([values.value-semantics](../05-values.md#values.value-semantics), [values.independent-copies](../05-values.md#values.independent-copies)). No other code can change a value that a function holds, so a function can be read and reasoned about alone. There are no move errors, no `Copy` trait and no `.copy()` method.

Affine moves, as Rust's moves and Hylo's `sink` parameters give, are the main alternative. They are rejected for core, because they add a class of errors for a performance property that the tools already show ([values.consumed-parameters](../05-values.md#values.consumed-parameters)). A value that must not be copied, such as a handle that the advanced tier hands to one task, is kept from copying by its inferred modes ([modes.bindings-and-axes](../13-modes.md#modes.bindings-and-axes)). Writing every copy as an explicit `.copy()` is rejected too, as noise: copies are cheap, so marking them adds nothing.

**How copies stay cheap.** None of this is part of the language, which fixes only what a program observes. It is the strategy that makes value semantics affordable:

- scalars and small aggregates are unboxed;
- heap objects are reference-counted: strings, lists, maps, the nodes of recursive types, and closures;
- writes use copy-on-write: an object that one reference holds is changed in place, and a shared one is copied first;
- so a copy costs O(1), one increment, and only a write to a shared object pays for a full copy;
- Perceus reuse analysis turns consumed parameters and unique references into updates in place.

The reference interpreter takes the simplest model that the rules allow. It represents every value as immutable OCaml data. It implements `inout` as copy-in, copy-out, and writes back on return and on raise alike. With the law of exclusivity ([modes.law](../13-modes.md#modes.law)), this can't be told apart from changing values in place.

Copy-on-write means that writing to shared data copies it. One pattern makes such a copy both silent and surprising: changing a list while a loop iterates over it. The law of exclusivity makes it an error ([modes.change-while-iterating](../13-modes.md#modes.change-while-iterating)). Any other write to a shared value copies it without a diagnostic.

A `str` is owned and immutable ([values.strings](../05-values.md#values.strings)), so a string behaves as every other value does, and comparing two strings compares their text. No tier has first-class references or lifetimes. A view into a string is a value of the advanced tier, which can't escape the function that holds the string.

`Shared<T>` is the one way to share mutable state with a common identity ([values.shared](../05-values.md#values.shared)). It belongs to the advanced tier, so core code keeps the local reasoning that value semantics gives.

## Passing values

A `let` argument never changes the caller's variable, whatever the callee does with its copy ([values.passing-values](../05-values.md#values.passing-values)). The compiler can still reuse memory when a caller hands over the last use of a value. To do so, it infers which parameters a function consumes ([values.consumed-parameters](../05-values.md#values.consumed-parameters)).

A written `own` mode is the alternative: the callee would reuse the argument's memory, with a warning where the caller kept using the place it passed. It is rejected because the caller can't observe the mode, so writing it would declare a compilation strategy in a signature. `let` and `inout` are the only modes. The cost is that a reader without tools doesn't see which arguments a function consumes. An edit to a body can change it, and with it how each caller passes the argument.

Which parameters a function consumes has no behaviour that a conformance test can observe, so the reference interpreter infers none of it. The conformance tests check what the rule guarantees: the caller's variable never changes, which reuse in place could break. The compiler's own tests check the inference.

An `inout` argument keeps every change the callee made, whether the callee returns, raises, or is ended by a handler ([values.inout-arguments](../05-values.md#values.inout-arguments)). Rolling `inout` arguments back on a raise is rejected. Exact rollback would mean copying every `inout` argument on entry to every function that can raise, which is a hidden cost. The cost of the rule is that a caller that catches the error sees a half-finished change. Code that needs all or nothing passes a copy, and assigns it back when the call succeeds.

## Evaluation order

Evaluation is strictly left to right ([values.left-to-right](../05-values.md#values.left-to-right)). C leaves the order of arguments unspecified, and Stilt fixes it. A program then has one meaning, two implementations print the same output, and a reader knows which side effect comes first. The rules go down to a called expression before its arguments, an indexed value before its index ([values.index-reads](../05-values.md#values.index-reads)), and each splice of a string shown before the next is evaluated. Each of these can print or panic.

An `inout` argument's place is read only when the call starts, after every argument ([values.inout-argument-order](../05-values.md#values.inout-argument-order)). So a change that a later argument makes to the place reaches the callee. In `xs.push(xs.pop() else 0)`, `pop` changes the list that `push` then receives. Reading the place in its argument's turn would lose that change, and write back a list that still holds the popped element. The cost is subtlety: the place's index expressions run in their turn, while the place itself is read later.

`place op= e` evaluates the place's index expressions once ([values.compound-assignment-order](../05-values.md#values.compound-assignment-order)), so `m[key()] += 1` calls `key` once. It reads the place only after `e`, as a plain assignment stores only after `e` ([values.assignment-order](../05-values.md#values.assignment-order)).
