# What you write, what is inferred

*This document describes how Stilt divides a program between what its author writes and what the compiler infers, and how the command line follows from the same division. The [Reference](../../reference/) is normative, and each rule below cites the paragraph that states it. The thesis comes from [Why Stilt is this way](../guide/10-design.md).*

Stilt's thesis is that a feature has one meaning and several compilation strategies. Taken strictly, it gives one test for everything a programmer writes:

> Write what a reader needs to check a function alone, and what changes what a program does. Everything else is a fact the compiler infers, shows next to the signature, and lets you limit. Every strategy is the compiler's choice.

The test shapes the language and its tools. Which parameters a function consumes is inferred, so `inout` is the one parameter mode written. A function passed as an argument brings its caller's effects, so a function that takes one writes no row variable, and marks it `escaping` only if it keeps it. One clause, `without`, limits the inferred facts that code can stay clear of, and a module's tier is inferred and shown, never declared. A program with errors still runs, up to the code that has them. And the compiler has seven commands.

## What is written

Five things pass the test, and nothing else does.

| Written | Where | Why it passes |
| --- | --- | --- |
| Types of parameters and results | Signatures | Types are inferred only inside a body, from the signatures it uses, so each function can be checked alone ([types.inferred-per-body](../../reference/07-types.md#types.inferred-per-body)) |
| The effects a function performs: `io` and `raise<E>` | Signatures | What a function may do to the world, and how it fails, is part of what it does ([effects.rows](../../reference/12-effects.md#effects.rows) and [effects.inference](../../reference/12-effects.md#effects.inference)) |
| `inout` | Parameters and arguments | It is the only mode a caller can observe: the callee's changes come back ([values.inout-arguments](../../reference/05-values.md#values.inout-arguments)) |
| `escaping` | Parameters of function type | Whether a function keeps its argument decides what the parameter's row means to callers, which inferring it from the body would hide from them ([effects.escaping-parameters](../../reference/12-effects.md#effects.escaping-parameters)) |
| `var` and `try` | Bodies | They show a reader where a value changes and where a call can fail ([modes.what-can-be-modified](../../reference/13-modes.md#modes.what-can-be-modified); [effects.raise](../../reference/12-effects.md#effects.raise)) |

## What is inferred

Every other fact about a function is inferred from its body, kept apart from the signatures that type checking reads, and shown by the tools ([facts.interfaces](../../reference/15-facts.md#facts.interfaces)). `stilt show` prints a function with its facts written in, each with the line that causes it, and a type with the one fact a type has, whether it can form a cycle.

| Fact | Inferred from |
| --- | --- |
| `panic` and `alloc` | The operations in the body and the functions it names ([facts.implicit-effects](../../reference/15-facts.md#facts.implicit-effects)) |
| `overflow` | The integer arithmetic in the body that can overflow, and the functions it names ([effects.overflow-effect](../../reference/12-effects.md#effects.overflow-effect)) |
| `div`, possible non-termination | `while` loops that aren't counting loops, `loop`s, calls through stored function values, recursion that neither descends nor shrinks, and the functions the body names ([facts.div](../../reference/15-facts.md#facts.div)) |
| `copy`, writes that copy shared data | Modifications that are shared, the arguments that a call copies for an in-place parameter, and the functions the body names ([facts.copy](../../reference/15-facts.md#facts.copy)) |
| `locks`, holding shared values | `when`s, and the functions the body names that run one ([shared.locks](../../reference/14-tasks.md#shared.locks)) |
| The capabilities below `io`: `fs`, `net`, `clock`, `env`, `console`, `rand`, `spawn` and `exec` | The natives the body names that have one, and the functions it names ([facts.capabilities](../../reference/15-facts.md#facts.capabilities)) |
| `unsafe` blocks and `foreign` functions | The `unsafe` blocks of the body's own code and the foreign functions it names, which no caller inherits ([c.unsafe-and-foreign](../../reference/20-builds.md#c.unsafe-and-foreign)) |
| The parameters a function consumes | What the body does with each parameter (below) |
| In-place parameters | The parameters whose storage a function limited by `without alloc` writes in place ([facts.own-storage](../../reference/15-facts.md#facts.own-storage), [facts.writes-in-place](../../reference/15-facts.md#facts.writes-in-place) and [facts.in-place-parameters](../../reference/15-facts.md#facts.in-place-parameters)) |
| The modes of locals, closures and parameters: locality, uniqueness, once, portability and contention | How each value is used, on an inferred lattice ([modes.bindings-and-axes](../../reference/13-modes.md#modes.bindings-and-axes)) |
| Where reference counts become atomic | The calls of `std.par` and `Shared.new`, the `when`s, and the `spawn`s and `task.scope`s whose function reaches a task's handle, which mark what other threads reach ([par.atomic-sites](../../reference/14-tasks.md#par.atomic-sites)) |
| A module's tier | The features its code uses ([program.module-tier](../../reference/04-programs.md#program.module-tier)) |
| Checks that can't fail, and loops and recursion that end | Six rules of acceptance, each a shape of code: a range loop, a guard, a divisor, a key, a counting loop and shrinking recursion ([facts.rules-of-acceptance](../../reference/15-facts.md#facts.rules-of-acceptance)) |
| Types that can form a cycle, and through which fields or variants | Whether a field's type holds a `Shared<U>` whose `U` holds the same `Shared<U>`, a function type or a type parameter ([cycles.can-form-cycle](../../reference/14-tasks.md#cycles.can-form-cycle)), printed at the type's first line |

A fact never changes what a program means. It records what the compiler chose and why, so a reader can see where values live, where they are updated in place, what may run in parallel, what authority a function holds, and which run-time checks can go. Of these facts, a package's API holds a module's tier and every fact that a `without` can name, `panic`, `overflow`, `alloc`, `div`, `copy`, `locks` and each capability, so a version whose function gains one needs a new major version and a dependency's patch never breaks a caller's limit. `unsafe`, which a `without` names too, limits a function's own code alone, so the API holds instead whether the package's own code holds an `unsafe` block ([c.unsafe-in-api](../../reference/20-builds.md#c.unsafe-in-api)). A version whose functions gain or lose any other fact needs no new version number ([versions.facts-in-api](../../reference/21-versions.md#versions.facts-in-api); [versions.limitable-facts](../../reference/21-versions.md#versions.limitable-facts)). Its facts are those a function has when verification proves nothing, so a version's number follows no proof ([versions.facts-without-proofs](../../reference/21-versions.md#versions.facts-without-proofs)).

## Consumption is inferred

```stilt
fn append_all(xs: List<i64>, ys: List<i64>) -> List<i64> {
  var out = xs
  for y in ys { out.push(y) }
  out
}
```

`stilt show` prints the fact that `append_all` consumes `xs`. A caller that passes its last use of a list gives the list up, and `push` grows it in place, with no copy.

- **What it means.** Nothing a program can observe. A caller may keep using the variable it passed ([values.passing-values](../../reference/05-values.md#values.passing-values)). The callee then gets a value that is still shared, and its first write copies it. Consumption decides only whether memory is reused, which is a strategy, so principle 1 keeps it out of the source.
- **How it is inferred.** A parameter is consumed when the body returns it, stores it in a value, rebinds it with `var`, passes it to a parameter that is consumed, or takes it apart to build in its place: a `match` on it, a value of a recursive type, whose arm builds a value of that type, as an insertion into a tree does, so that the node it matched can become the node it builds. Lean 4 infers the same split between owned and borrowed parameters ([Ullrich and de Moura](https://arxiv.org/abs/1908.05647)), and `stilt-rc` infers borrowing inside each function.
- **Where the fact lives.** Apart from the signature, like `alloc` and `panic`. Type checking never reads it, so editing a body re-checks none of its callers (goal `body-edits-recheck-one-body`).
- **The calling convention follows the fact.** An edit that starts or stops consuming a parameter changes how callers pass it, so the patch recompiles those callers too, which the query database finds. Every other edit patches one function (`edit-to-running-program`).
- **Lost reuse is a fact too.** When a caller keeps using a place it passed to a consumed parameter, after the call or in the call itself, the callee can't reuse its memory. Nor can it when the place is an `inout` parameter, which goes back to the caller when the function returns or raises, and some path from the call gets there without assigning the whole parameter ([values.inout-arguments](../../reference/05-values.md#values.inout-arguments)). `show` reports it at the call, the way it reports an allocation at the line that causes it, but as a fact of its own: it adds nothing to `alloc`, whose operations [facts.allocation](../../reference/15-facts.md#facts.allocation) lists, so `without alloc` doesn't limit it. The lint for writes that copy shared data reports it as one of them.
- **Changing a parameter.** A callee that changes a parameter first rebinds it with `var x = x` ([modes.what-can-be-modified](../../reference/13-modes.md#modes.what-can-be-modified)). Whether that copies is again the caller's last use.

A written mode, `own`, was weighed and rejected. It would show a reader without tools which arguments a function consumes. But it states a strategy that no observation can tell apart, and a body that starts reusing its argument would need an edit to its signature, which re-checks every caller. [facts.inferred-facts](../../reference/15-facts.md#facts.inferred-facts) makes the same trade for `alloc` and `panic`, and `show` prints the fact as plain text, for agents and reviewers alike. Affine moves, as in Rust and Hylo's `sink`, were rejected too: they add a class of errors for a property that the tools already show ([values.consumed-parameters](../../reference/05-values.md#values.consumed-parameters)).

## A function argument's effects pass through

```stilt
fn twice(x: i64, f: fn(i64) -> i64) -> i64 { f(f(x)) }

fn halve(n: i64) -> i64 / raise<str> {
  if n % 2 != 0 { raise "{n} is odd" }
  n / 2
}

fn main() / {io, raise<str>} {
  let n = try twice(12, halve)
  print("{n}")
}
```

`twice` names no effect, yet `main` may pass it `halve`, which raises. The `try` that marks the failure sits in `main`, where the program can fail.

- **Pass-through.** The row written on a function parameter lists what the callee itself takes charge of. Whatever else the argument performs passes through: the call performs it in the caller, and the caller marks it ([effects.non-escaping-parameters](../../reference/12-effects.md#effects.non-escaping-parameters)). The parameter is checked as though its row held a row variable of its own, which the function's own row holds too, so the soundness argument of row variables applies unchanged.
- **Non-escaping by default.** Such a parameter may only be called, or passed on to another non-escaping parameter, directly or in a closure literal. A parameter that passed its effects through and was kept would carry its caller's effects where no row records them, so keeping one is an error, E0508, which offers the fix of writing `escaping`.
- **`escaping` parameters.** A function that keeps a parameter marks it `escaping`, as Swift does, and its row is exactly the one written: `fn button(label: str, escaping on_click: fn() / io) -> Button`. Where it stays generic in the kept function's effects, it writes a row variable there, paired as [effects.paired-row-variables](../../reference/12-effects.md#effects.paired-row-variables) and [effects.passing-to-paired-variables](../../reference/12-effects.md#effects.passing-to-paired-variables) ask: `compose`, which returns a closure that calls both its arguments, or a memoizer that stores one. These are rare in `core`. The rule reads one body, as OxCaml's locality inference does ([Lorenzen et al., ICFP 2024](https://dl.acm.org/doi/10.1145/3674642)), and Effekt builds a whole language on the same split between called and stored functions ([Brachthäuser et al., OOPSLA 2022](https://plg.uwaterloo.ca/~e45lee/publication/boxes/boxes.pdf)).
- **Handling an argument's failure.** A callee that handles its argument's failures says so in the parameter's row:

  ```stilt
  fn or_zero(f: fn() -> i64 / raise<str>) -> i64 {
    try f() catch _ because "a failure counts as zero" => 0
  }
  ```

  `raise<str>` is `or_zero`'s to handle, so its `try` marks the call and its `catch` catches. Anything else the argument performs, such as `io`, passes through to the caller. A `catch` around a call whose failures pass through is E0506, which offers the fix of writing `raise<E>` in the parameter's row.
- **Compilation.** Raises compile to tagged returns. A pass-through call propagates the tag it gets back, as a call through a row variable would, so the success path costs the same (`free-success`).

The cost is that `fn(A) -> B` reads two ways. On a non-escaping parameter, the row lists what the callee handles. Everywhere else, in a record field, a result or an `escaping` parameter, it is the whole row. The rule fits in one sentence and has one error, for a non-escaping parameter that is kept, but it is a second reading of the same text, so its diagnostics are approved as snapshots before its record is.

Row variables on every higher-order function were weighed and rejected. They restate at each definition what each call site already shows, and every callee that catches needs the paired row variables' and the passing rules' pairing. So were inferring which parameters escape from the body, which would make callers' typing depend on it, and telling kept parameters apart by a written row variable, which couldn't express a kept callback with a fixed row.

## One clause limits inferred facts

```stilt
module dsp.filter
  without panic

fn step(s: State) -> State without alloc { … }
```

- **Implicit effects.** `without panic` rules out every panic but integer overflow, which `without overflow` rules out, and `deadlock`, which a `when` reached through a function value may meet ([effects.without-panic](../../reference/12-effects.md#effects.without-panic) and [effects.without-overflow](../../reference/12-effects.md#effects.without-overflow)). `without alloc` rules out allocation, in `core` as in every tier ([facts.without-alloc](../../reference/15-facts.md#facts.without-alloc)). A native function, which has no body to read, allocates unless the Reference lists it as one that doesn't ([facts.native-allocation](../../reference/15-facts.md#facts.native-allocation)), so a function the library adds can't escape the limit unseen. `without panic, div` means total, `without net` rules out a capability, and `without copy` rules out writes that copy shared data.
- **Unsafe code.** `unsafe` blocks and foreign calls are inferred facts like `panic` and `alloc`, shown next to each signature. A foreign call also counts what any C code may do, `panic`, `alloc` and `div`, and every capability when it performs `io`, unless its declaration's `without` clause states less, which `stilt show` marks as trusted ([c.effects](../../reference/20-builds.md#c.effects)). `without unsafe` rules them out of a module or a function, and a package's manifest can rule them out of its dependencies, as Rust's `#![forbid(unsafe_code)]` and dependency audits do.
- **Tiers aren't limits.** A module's tier is inferred from the features it uses and shown as its implicit effects are, and no syntax names, chooses or limits it ([program.module-tier](../../reference/04-programs.md#program.module-tier)). Keeping unsafe code out, the one reason to limit the `systems` tier, belongs to the facts of unsafe code, which `without unsafe` names.
- **On a module or a function.** A module's limit covers every function in it, while its tests and doc examples are exempt, so they may use `assert`. A function's limit covers its body and the functions it names. A call through a function value adds nothing to the caller's facts: they were counted where the closure was written or the function was named ([facts.calls-through-function-values](../../reference/15-facts.md#facts.calls-through-function-values)).
- **One check and one diagnostic.** A limit is an inferred fact that must stay below it. The diagnostic names the fact, where it comes from, and the limit: "`step` allocates at line 12, where `out.push(y)` may grow `out`; its signature says `without alloc`." A new kind of fact needs no new keyword and no new code. Where a rewrite keeps an operation within the limit, as `get` with a fallback does for an index, the diagnostic offers it as a fix.
- **In place, shown.** A function that consumes an argument updates it in place whenever its caller passes its last use, and `show` names each call that loses that reuse, with why ([values.consumed-parameters](../../reference/05-values.md#values.consumed-parameters)). Under `without alloc`, a write through an index to a list the function holds the own storage of, an `inout` parameter or a `let` parameter it takes at its last use, is in place, and so is a write through an element's fields when the elements hold no string, list, map, function or recursive value, and `show` prints the parameter `in place`. The copy that a shared argument needs moves to the call, where it allocates in the caller ([facts.copy-at-call](../../reference/15-facts.md#facts.copy-at-call) and [facts.writes-in-place](../../reference/15-facts.md#facts.writes-in-place)). Koka's `fip` can promise reuse because its callers must hand over unique values ([FP², ICFP 2023](https://www.microsoft.com/en-us/research/uploads/prod/2023/05/fbip.pdf)); a Stilt caller keeps value semantics, and pays for the copy at its call when it keeps the value.
- **Verification proves facts away.** `check` proves an operation safe when its code has one of six shapes, each with a name that E0204 and `show` print ([facts.rules-of-acceptance](../../reference/15-facts.md#facts.rules-of-acceptance)): a **range loop**, `xs[i]` in `for i in 0..xs.len()`; a **guard**, `xs[i]` under `if i >= 0 && i < xs.len()`; a **divisor**, `n / d` under `if d != 0`; a **key**, `m[k]` under `if m.contains(k)` or after `m[k] = v`; a **counting loop**, `while i < n { …; i += 1 }`; and **shrinking recursion**, `count(n - 1)` under `if n > 0`. A check so proved can't fail and adds no `panic`, and a loop or self-calls so shown to end add no `div`. Nothing is written for it, and nothing it proves leaves the body. So a module can say `without panic` and still index lists:

  ```stilt
  fn total(xs: List<i64>) -> i64 without panic {
    var s = 0
    for i in 0..xs.len() { s += xs[i] }
    s
  }
  ```

  `xs[i]` is in a range loop, so it can't panic, and `show` prints `proved bounds by a range loop` where the panic would have been. Over `0..xs.len() + 1`, the index is E0204, whose message names what the closest rule needs: ``a range loop needs it to end at `xs.len()`, not at `xs.len() + 1` ``. The rules read only what a reader sees, so a function's size or the joins of its branches never change what checks. An analysis of the differences between a body's integers, lengths and keys, with no solver and no timeout, proves more, as a binary search's middle, but changes no fact: it only lets release builds drop more checks. A proved check can't fail, so a debug build, which keeps it, behaves as a release build does, which drops it.

A header option for each fact, such as `total` or `noalloc`, and a keyword for each promise, such as `fip` or `local`, were weighed and rejected. Each compares an inferred fact with a limit, so separate syntax would cost a keyword, a rule and a diagnostic for every new fact. Declaring a module's tier, to unlock it or to limit it, was rejected as well: tiers are inferred and shown, and a declaration would make the programmer state what the features already decide ([program.module-tier](../../reference/04-programs.md#program.module-tier)).

## A program with errors still runs

- **What runs.** `run` runs every program. Each function, test or constant with an error panics with kind `check-error` where it is reached, and the run exits with status 2 whenever the program has an error, so no script mistakes it for success ([conformance.run-statuses](../../reference/01-conformance.md#conformance.run-statuses) and [errors.running](../../reference/18-errors.md#errors.running); [program.programs-with-errors](../../reference/04-programs.md#program.programs-with-errors) and [program.check-error-report](../../reference/04-programs.md#program.check-error-report)). Holes work the same way: a hole warns with W0300, and panics with kind `hole` only if it is reached.
- **Everywhere alike.** The reference interpreter runs a program with errors as the compiler does, so conformance tests cover it.
- **Recovery is specified.** The Reference specifies total error recovery after Hazel's marked lambda calculus: every program gets a type, each error is marked where it is, and checking continues around it ([Zhao et al., POPL 2024](https://hazel.org/papers/marking-popl24.pdf)). Which diagnostics are root causes then follows from the marking ([errors.root-causes](../../reference/18-errors.md#errors.root-causes)).

Refusing to run a program with errors was weighed and rejected: a half-fixed program couldn't be tried, and agents fall back on commenting code out. A run that stops at a reached error and always exits with status 2 keeps what refusing gave, since code that fails its checks never appears to work. An option that only debug builds accept was rejected too: it would give the language two behaviours, one of which no conformance test could see.

## Seven commands

The command line follows the same test: a flag that picks a strategy, or a command that shows one more view of the same facts, shouldn't exist. Seven commands work on a program's code: `check`, `run`, `test`, `build`, `show`, `fmt` and `migrate`. [The command line](../commands.md), written from `stilt help`, gives every command of `stilt` with its options.

- **One engine.** Every command, the language server and every running program share one query database (`one-engine`). So `run` receives each edit of its files and patches it into the running program (`edit-to-running-program`) until the program ends, and then ends with its status, and `repl` is the REPL, evaluating expressions and `let`s in a module's scope, whose bindings keep their values as the program's code is patched under them (`interactive-evaluation`; [repl.sessions](../../reference/19-tools.md#repl.sessions)).
- **`show` prints every view.** A module shows as its skeleton, signatures and doc summaries. A function shows under its module's header, which has the module's tier written in, with its inferred local types and facts written in, and its macros expanded. A part shows the context of each of its holes after it, in the order Hazel measured ([Agent syntax](agent-syntax.md), "Typed holes as context"), a diagnostic code its explanation, and an `unsafe` block its justification. With `--release`, `show` prints each function's performance report in its release build: the instantiations it is compiled for, each call left on a dictionary with its reason, the reference-count operations and the copies that its code still performs, the checks that verification proved and dropped and those kept, each by line, and the lines of the program's profile that the build dropped since their bodies changed ([builds.performance-report](../../reference/20-builds.md#builds.performance-report)).
- **`check` includes verification.** `check` verifies each body as it checks it, reading signatures and never another body, and the engine keeps what it proves with the body's other facts, so `check` reports it beside the errors.
- **Edits go through `check` and `test`.** An address with a hash, such as `main.totals/body#a91f`, is an edit. The command reads the new text from standard input, applies it if the hash still matches and the text parses, and answers with the verdict that follows ([Agent syntax](agent-syntax.md)).

Among the flags, `run --profile` and `test --profile` count how often each body, arm and loop runs and add the counts to the program's profile, text kept beside it that release builds read as hints ([builds.profile-use](../../reference/20-builds.md#builds.profile-use)). Three commands are internal: `parse --sexp`, which `just parse` uses; `engine`, the process that holds a program's database between commands, which the tools that keep a program open start ([Compiler architecture](compiler-architecture.md), "The engine"); and `lsp`, the language server that an editor starts, which asks the program's engine.

A command for each view, such as `skel`, `context`, `expand`, `explain`, `complete` or `audit`, was weighed and rejected: each would show facts of the same database, with options of its own to learn. So were `--watch` and `--keep-going`, which would each switch on a behaviour that should always hold, and a separate `verify` step, which would keep what it proves out of the edit loop.

## The theorem behind it

The [Lean model](../../formal/) proves `inPlaceAgreement`: on a well-typed program that obeys the law of exclusivity, copy-in, copy-out and in-place mutation give the same observation. So an `inout` argument has one meaning however it is passed, and passing it in place is a strategy.

The model also proves the converse for the Reference's call rule (`pairwiseDisjoint_greatest`). A rule that judges a call by the shapes of its `inout` arguments, as [modes.overlapping-inout](../../reference/13-modes.md#modes.overlapping-inout) does, and that keeps the two models in agreement, accepts no call that the Reference rejects. The witness for each rejected call is a well-typed program whose callee writes through one argument and indexes a list with what it reads through an overlapping one, so that it returns `()` under copy-in, copy-out and panics with the kind `bounds` in place. So the Reference's rule is the most permissive sound rule of its kind, and the law of exclusivity is exactly what in-place mutation needs. The model also proves that handing a variable's storage over at its last use agrees with copying it (`movingAgreement`), which is the formal ground of inferred consumption.

The theorem is relative to what the Reference looks at. [modes.overlap](../../reference/13-modes.md#modes.overlap) removes indexes before comparing places, so `swap(inout xs[0], inout xs[1])` is rejected although it is safe; a rule that saw index values could accept more. E0404, which forbids changing a list inside a loop over it, is outside the theorem: the model's loop iterates the value it started with, so E0404 prevents a hidden copy, not a difference in meaning ([modes.change-while-iterating](../../reference/13-modes.md#modes.change-while-iterating)).

## The later tiers

The later tiers keep the same division, and each adds facts rather than annotations. The [design sketch](design-sketch.md) and [Values with inferred costs](values-and-costs.md) describe them.

- **Modes.** Every binding has a point on each of five axes, locality, uniqueness, once, portability and contention, inferred and shown ([modes.bindings-and-axes](../../reference/13-modes.md#modes.bindings-and-axes)). The advanced tier's features demand them: thread safety follows from the modes, so no type says it may cross threads.
- **Views.** Slices and iterators are views that can't escape ([views.what-view-is](../../reference/13-modes.md#views.what-view-is) and [views.escaping](../../reference/13-modes.md#views.escaping)), and their dependence on a parameter is inferred from the signature, so nothing writes a lifetime. A view made through `inout` writes its source, which is inferred and shown as what a view reads is, and a projection hands a place back, written only as its result `inout T`, since whether a call is a place is part of the signature ([projections.call-is-place](../../reference/13-modes.md#projections.call-is-place) and [projections.declaring-projection](../../reference/13-modes.md#projections.declaring-projection)).
- **Capabilities.** `io` stays the one effect a signature writes for the world. The capabilities below it, `fs`, `net`, `clock`, `env`, `console`, `rand`, `spawn` and `exec`, are inferred from the natives a function reaches and shown, `without` limits them, and a manifest grants a dependency exactly those its code uses ([facts.capabilities](../../reference/15-facts.md#facts.capabilities) and [facts.capability-grants](../../reference/15-facts.md#facts.capability-grants)).
- **Checked promises.** `div` and copies of shared data are facts like `alloc`, and `without` makes each a promise.
