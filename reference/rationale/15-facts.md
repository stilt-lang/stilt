# Rationale: Inferred facts and limits

Stilt promises no hidden costs: whether code can fail, allocate, loop forever, copy, block or reach the world is visible. It also promises that a function is checked from its signature alone. The two pull against each other, since most of these costs are facts of bodies. This chapter settles the conflict the same way for every cost. The compiler infers each cost from the body as a fact, keeps the fact apart from the signature, and shows it next to the signature. Code can then promise with `without` to stay clear of it.

## Inferred facts

Allocation is too common to declare. Nearly every function allocates, so a required `/ alloc` would sit on almost every signature and stop meaning anything. Panics are nearly as common. So `panic` and `alloc`, and the facts that join them, are inferred and never written ([facts.implicit-effects](../15-facts.md#facts.implicit-effects), [facts.inferred-facts](../15-facts.md#facts.inferred-facts)).

They also stay out of the signatures that type checking reads ([facts.interfaces](../15-facts.md#facts.interfaces)). If they were part of a signature, editing a body could invalidate every caller, and incremental checking depends on that never happening. Koka puts effects such as `div` and `exn` in function types. The implicit effects could go into Stilt's function types the same way, as hidden variables. That would make `without alloc` exact for higher-order code. But the variables would enter type checking, and a body that gains an allocation would change a type that every caller is checked against.

A call through a function value adds nothing ([facts.calls-through-function-values](../15-facts.md#facts.calls-through-function-values)): the effects of the value are counted where it is written or named. Every panic, allocation and capability then belongs to the module whose source holds it. A higher-order function such as `List.fold` keeps a caller's limits whatever callback it is given. The cost is that a limit covers the code's own source text alone. Code under `without panic` may call a function value created in another module, even one that panics.

A body with an error has no facts ([facts.bodies-with-errors](../15-facts.md#facts.bodies-with-errors)). It runs only up to its error, where it panics with `check-error`. Reporting what it would have done would turn one mistake into errors in every caller under a limit.

## Showing facts

A fact that nobody sees is a hidden cost, so the tools print every fact beside the signature and at the line that causes it ([facts.visibility](../15-facts.md#facts.visibility)). The facts suite ([facts.facts-suite](../15-facts.md#facts.facts-suite)) pins what they print, derived from the rules by hand. Both the rules and the tools are then checked against an expectation that no implementation produced.

## Limits

One clause, `without`, turns any of these facts into a promise, on a module or on a single function ([facts.without](../15-facts.md#facts.without)). Separate header options, such as `total` and `noalloc`, are the alternative. They would give two spellings of one check, and no way to limit a single function. The check is local: it reads facts that inference has already recorded, so a limit costs almost nothing to check, and one diagnostic serves every limit.

A limited function counts as one without the fact wherever it is named. A mistake in it is then reported once, where it is written, and not again in every caller. Operations on one line beyond one limit give one E0204, since one rewrite of the line fixes them all.

Test bodies, doc examples and properties are exempt, since they check the code and don't ship with it, and `assert` panics by design.

The limits are contextual keywords ([facts.spelling](../15-facts.md#facts.spelling)), so words such as `copy`, `div` and `env` stay usable as names everywhere a limit can't stand.

## Panics, overflow and allocation

The operations that allocate are listed by what the source shows ([facts.allocation](../15-facts.md#facts.allocation)). They are literals that build a list, a closure or a string, and constructors of recursive types, which live on the heap. Writes through an index allocate too, since they copy a list or a map that is shared. The library's natives are judged by their signatures ([facts.native-allocation](../15-facts.md#facts.native-allocation)), since their bodies aren't Stilt.

`without alloc` is conservative ([facts.without-alloc](../15-facts.md#facts.without-alloc)). A `push` counts as allocating even when the list isn't shared and has room, since neither is known before the program runs. An assignment through a map element, as `m[k].f = v`, reads the element before it stores it back ([facts.map-element-places](../15-facts.md#facts.map-element-places)), so it can panic as the read can.

## Updates in place

A function that consumes a list should be able to promise that it updates the list in place. `without alloc` alone can't express that, since a write through an index allocates whenever the list may be shared. Koka's `fip` makes such a promise by requiring callers to hand over unique values. A Stilt caller keeps value semantics, so the copy that a shared argument needs has to happen somewhere. Stilt puts it at the call, in the caller ([facts.copy-at-call](../15-facts.md#facts.copy-at-call)), where the lost reuse already explains it. The callee then holds its own storage ([facts.own-storage](../15-facts.md#facts.own-storage)), writes in place ([facts.writes-in-place](../15-facts.md#facts.writes-in-place)), and keeps its promise at run time ([facts.in-place-promise](../15-facts.md#facts.in-place-promise)).

Three alternatives are rejected:

- **Copying in the callee,** whenever its argument turns out to be shared. This would break the promise, since a function limited by `without alloc` would still copy at run time.
- **Requiring callers to hand over unique values,** as `fip` does. A caller that keeps using its value would be an error, where value semantics promise a copy.
- **Giving every function in-place parameters.** This would shift the cost of a copy from callee to caller in all code, beyond the code behind a promise. It would also change the facts of every function that writes an `inout` list, for no limit that reads them.

Writes through the fields of an element are in place only when the elements hold nothing on the heap. An element that holds a string or a list may share it with another element, so writing into it would copy. A type parameter may stand for such a type, so an element type that holds one counts as one. This still lets a simulation's step over a list of particles write each particle in place. The other places through an index allocate for their own reasons. A store into a map may insert a key. An `inout` argument `b[i]` or a `yield` of `b[i]` hands the element on to code that may keep it.

## Termination

`without panic` doesn't promise that code ends. Possible non-termination is the fact `div` ([facts.div](../15-facts.md#facts.div)), so `without panic, div` means total ([facts.without-div](../15-facts.md#facts.without-div)). Total code rules out every failure but overflow and running out of stack or memory, which no checker rules out without proofs about values.

Recursion that descends into the structure of its data ends ([facts.descending-self-calls](../15-facts.md#facts.descending-self-calls)), since a chain of strict parts of a value ends. The check is lexical and needs no facts about values. The Lean model proves, in its core calculus, that every call of a function whose self-calls pass it ends (`Decls.Ranked.call`, `formal/Stilt/Ends/`), while `f(x) = f(x)`, which the check rejects, never does. Loops and recursion on integers end when verification shows them to count toward a bound or shrink toward one ([facts.counting-loops](../15-facts.md#facts.counting-loops), [facts.shrinking-recursion](../15-facts.md#facts.shrinking-recursion)). The test must bound the parameter, and a test of equality doesn't: `count(n - 1)` under `n == 0` fails to end for `count(-1)`.

A call through a stored function value is a site of `div`, unlike the other facts, since a loop through a record of closures would otherwise check as total. A `for` loop ends, since what it iterates is finite and nothing changes it while it runs.

Two alternatives are rejected:

- **A `while` with a variant expression,** a decreasing measure that the programmer writes, as Dafny and Why3 ask for. It is an annotation, and inferred facts take none.
- **`div` and `copy` in rows.** They would make facts of bodies part of signatures, which type checking reads.

`div` stays conservative. Recursion that doesn't shrink and `while` loops that don't count are taken as possibly diverging, though most of them end. Code written for the limit recurses on its data, moves a number toward a bound, or loops with `for`.

## Copies

A write to a value that a copy still shares copies it, and the modes already show such writes as `shared`. `without copy` ([facts.without-copy](../15-facts.md#facts.without-copy)) forbids them, so hot code can rule out hidden copies while it still allocates fresh values ([facts.copy](../15-facts.md#facts.copy)). A warning on every write that copies is the alternative. It is rejected because writing to a copy is the ordinary, correct use of value semantics, so the warning would fire on copies the programmer wants.

## Capabilities

`io` is the one effect a signature writes for the world, and it says nothing about which part of the world a function reaches. A function that reads the clock and one that deletes a directory both say `/ io`. Capabilities below `io` ([facts.capabilities](../15-facts.md#facts.capabilities)) are inferred from the natives a function reaches ([facts.capability-natives](../15-facts.md#facts.capability-natives)), shown, and limited. So a module can promise that it never opens a socket. A manifest can grant a dependency exactly the capabilities its code uses ([facts.capability-grants](../15-facts.md#facts.capability-grants), [facts.ungranted-capabilities](../15-facts.md#facts.ungranted-capabilities)). A dependency that only prints is granted `console`, and the fix that E0608 offers is the narrowest grant.

Four alternatives are rejected:

- **Capabilities in rows,** as `/ {fs, clock}`. They would grow every signature that performs `io`, and a body edit that reaches a new native would change a signature and check every caller again.
- **Counting capabilities at calls through function values,** as `div` counts calls through stored ones. `without fs` would then rule out every stored callback, even one that only prints, and give a capability to whoever calls a closure, where it belongs to whoever wrote it.
- **A capability of `exit`,** such as `process`. It would grant nothing, since `exit` reaches nothing outside the process ([facts.io-and-capabilities](../15-facts.md#facts.io-and-capabilities)).
- **Finer capabilities,** such as `fs.read` apart from `fs.write`. Eight coarse ones are what a reader of a manifest can review.

A function's capabilities are limitable facts of its package's API. A version whose function gains one needs a new major version, so `without clock` can't break through a dependency's patch.

## Verification

A function that indexes a list can panic with `bounds`. Without proofs, code limited by `without panic` couldn't index a list, and every `while` would have `div`, even one that plainly counts. A release build that keeps every check also pays for the ones that can't fail. Verification proves such facts inside `check`, from each body alone ([facts.verification](../15-facts.md#facts.verification)). A proof changes what is inferred ([facts.what-proofs-change](../15-facts.md#facts.what-proofs-change)), so `without panic` accepts an index proved in range.

Its facts are inferred, never written. Refinements or invariants written on types or functions, as in Liquid Haskell or Ada's SPARK, are permanently rejected, since facts in Stilt are inferred. Proofs that only remove checks in release builds, and change no fact, are rejected too: `without panic` still couldn't index a list, and the work would be done without the promise it allows.

Verification has two parts, and the split is the central choice. What `check` accepts follows six rules that a person can learn, each a shape of code with a name. A reader can predict every verdict, and an error names the rule it misses. An analysis proves more, and release builds alone read it, to drop checks that can't fail. The alternative is to let the analysis decide what `check` accepts. It is rejected because a person can't predict its verdicts, which hang on thresholds, joins and a pair dropped at a loop's sixth visit. An edit that means the same, as a test moved into a function, could lose a proof and break a limit. A second implementation would have to copy the algorithm exactly.

A proved check can't fail, so a release build that drops it behaves as a debug build and the reference interpreter do, which keep every check. A wrong proof therefore shows as a difference between a release build and the other two, which three-way differential testing reports. A body's facts and proofs are queries of that body. An edit proves again only the bodies it changes, and the functions whose `panic` or `div` it changes are checked again where they are named. A debug build uses none of these proofs: its optimizer drops checks by an analysis of its own, which no rule fixes. The reference interpreter needs no analysis at all, since it reads the rules of acceptance alone.

A package's API reads `panic` and `div` as they are with nothing proved. A version's number then never depends on what verification proves, which an edit that means the same, or a better analysis, can change.

## The rules of acceptance

The six rules ([facts.rules-of-acceptance](../15-facts.md#facts.rules-of-acceptance)) cover the shapes in which code that can't fail is written:

- an index in a loop over the list's range ([facts.range-loops](../15-facts.md#facts.range-loops));
- an index under a test ([facts.guards](../15-facts.md#facts.guards));
- a division under a test of its divisor ([facts.divisors](../15-facts.md#facts.divisors));
- a map read after a test or a store of its key ([facts.keys](../15-facts.md#facts.keys));
- a loop that counts toward a bound ([facts.counting-loops](../15-facts.md#facts.counting-loops));
- recursion that shrinks toward one ([facts.shrinking-recursion](../15-facts.md#facts.shrinking-recursion)).

Each reads only the text, the names and their types, so a body's size and the shape of its branches change nothing it accepts. When a rule misses, the error names the closest rule and the first condition the code doesn't meet ([facts.closest-rule](../15-facts.md#facts.closest-rule)). Its fix is a rewrite into the rule's shape, or a read through `get`.

More rules are left out: for a list literal at a literal index, `insert`, `remove`, `slice` and `swap`, a `match` on a divisor, or a binary search's middle. Each would be one more shape to learn, and the analysis proves them for release builds. Some checks stay, as they stay in the equivalent Rust. Among them are an index from a parameter with no test, an index into a row of a list of lists, and an index that multiplies, as `cells[y * n + x]`. A binary search's middle stays too, and the analysis proves it for release builds alone.

Keys are proved only for types whose `Eq` and `Hash` are a primitive's or structural. A written `eq` may answer `false`, or change its answer, so a key once stored may not be found again. The bindings of a `when` are no places for these rules. Two names of one `when` may reach one value, so a fact about one says nothing once the other is written. Termination by size-change graphs is rejected because a graph's verdicts are hard to explain in a message. A measure that the programmer writes is an annotation.

## The analysis

Three alternatives are rejected:

- **An SMT solver such as Z3.** It decides more arithmetic than the analysis does, but its verdicts depend on its version, its limits and the text of each query. Two implementations would have to send the same queries to the same solver, and a new version of either could change what compiles.
- **Bounds-check elimination as compilers do it,** as Go's prove pass or ABCD. It is defined by an implementation's intermediate representation, so no specification could fix its verdicts for two implementations, and both Go's and Swift's have removed checks unsoundly.
- **Liquid types,** refinements inferred on signatures as well as bodies. They would make callers depend on a callee's body, and inside a body they compute what differences compute directly.

The analysis instead follows differences between integers ([facts.terms](../15-facts.md#facts.terms), [facts.difference-facts](../15-facts.md#facts.difference-facts)), a domain whose closure is exact, with no search and no timeout (Miné, 2001). Intervals alone can't prove `i < xs.len()` for an `i` and a length that both vary. Octagons, facts `±t ± u ≤ c`, prove `i + j < n` without the bound on lengths, but cost more per body. Differences prove the checks of the benchmark suite. The greatest length of a list ([facts.greatest-length](../15-facts.md#facts.greatest-length)) is what lets two indexes in range add without overflow.

A closed set already holds every fact between the terms it keeps, so dropping the terms that are no longer live at the end of a statement loses nothing ([facts.difference-facts](../15-facts.md#facts.difference-facts)). The facts a body keeps then stay as few as its live values. Every implementation drops the same terms at the same points, so each reaches the same verdicts. The bindings of a `when` get no terms ([facts.terms](../15-facts.md#facts.terms)) for the reason they are no places for the rules of acceptance.

Widening at fixed thresholds ([facts.widening](../15-facts.md#facts.widening)) makes the analysis of loops end. Widening with no thresholds is rejected: a loop's bound would be lost at its second visit, and `while k <= m` wouldn't keep `k ≤ m + i`. The cap on large bodies ([facts.large-bodies](../15-facts.md#facts.large-bodies)) bounds the cost of the rest. A body of 40 terms and 300 statements, with each loop visited about four times, closes about two million pairs: a millisecond or two. Only release builds run the analysis.

Overflow is proved by the analysis alone ([facts.proved-overflow](../15-facts.md#facts.proved-overflow)), and no proof of it changes what `check` accepts. Overflow is a fact of its own, which `without overflow` limits, and release builds drop its checks where they can.
