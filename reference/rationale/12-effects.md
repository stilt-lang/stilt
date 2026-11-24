# Rationale: Effects and handlers

Stilt has no exceptions and no null. Every way a function can fail or touch the world appears in its type, after `/`, and every call that can fail is marked with `try`. The rules of this chapter decide which effects a row can name, how rows combine and are inferred, and which parameters pass their arguments' effects through to the caller. They also decide what `try`, `catch` and `raise` mean, how failure kept as data relates to raising, and which panics `without panic` rules out. The advanced tier adds effects whose meaning the caller chooses, with handlers that implement them.

## Rows

A row lists the effects a function may perform beyond computing its result ([effects.rows](../12-effects.md#effects.rows)). Core needs only two labels: `io`, for whatever reaches the world, and `raise<E>`, for failure to the caller. `panic` and `alloc` are effects too, but they are inferred and never written ([effects.other-effects](../12-effects.md#effects.other-effects)). Allocation is too common to declare: a written `/ alloc` would sit on almost every signature and mean nothing.

A row holds one `raise` label ([effects.repeated-elements](../12-effects.md#effects.repeated-elements), [effects.one-error-type](../12-effects.md#effects.one-error-type)). The alternative is several labels, kept apart by scoped labels as in Koka. Several labels make the type of a catch-all's variable unclear, since a `catch e` would have to say which of the errors `e` is. They also ask every reader, and every agent that writes code, to learn how labels scope. With one label, code that can fail in two ways maps one error into the other where they meet, usually with `try … catch e => raise …`. A function that reads a file and parses it wraps `io.IoError` in its own error type at the `fs` call. Several labels would only accept rows that are errors under the single label, so a program written for one label means the same under either.

Row variables are declared only by functions ([effects.row-variables](../12-effects.md#effects.row-variables)). A type or an impl has no body whose effects a variable could stand for. Functions that keep functions, as `compose` does, are the only code that needs to stay generic in what its arguments perform.

## Inference

A body's effects are inferred and checked against the declared row ([effects.inference](../12-effects.md#effects.inference)). A signature then tells a reader whether a function fails and whether it reaches the world, without the body being read, and the body never restates what its calls perform. A closure literal performs nothing where it is written: its effects happen when it is called, so they belong to its type.

Each missing effect is reported once per row, at the first place that performs it ([effects.missing-effects](../12-effects.md#effects.missing-effects)). A function that prints ten times without `io` has one mistake, and one diagnostic says so. The fix is the same whichever call is blamed. Where two function types must be one and their rows would raise two types ([effects.rows-that-meet](../12-effects.md#effects.rows-that-meet)), the error goes where the second type arrives. A function value whose type is already formed can only mismatch. A closure literal is checked against the type that the first branch set, so its own `raise` is the mistake.

## Function values

A function value with a smaller row fits where a larger one is expected ([effects.function-values](../12-effects.md#effects.function-values)): a pure function can stand wherever a callback that may print is accepted. The row grows only where a value is checked against an expected type, and function types inside other types must match exactly. Growing rows inside a `List<fn()>` would make a list of pure functions a list of printing ones. A callee could then fill it with printing functions, which the caller, still holding a `List<fn()>`, would call as pure. For the same reason an `inout` argument's row is exact ([effects.inout-function-arguments](../12-effects.md#effects.inout-function-arguments)): the callee may store a function with the larger row in the caller's place, which the caller then sees.

## Parameters that pass effects through

Higher-order functions are written without row variables ([effects.non-escaping-parameters](../12-effects.md#effects.non-escaping-parameters)). `map`, `fold` and `Result.of` take functions whose rows name only what they take charge of. Every other effect of the argument passes through to the caller, which sees, marks and handles it as if it had made the calls itself. The alternative is a row variable on every higher-order parameter, as in `map<U, e>(self, f: fn(T) -> U / e) -> List<U> / e`. Every signature would then restate effects that each call already shows, and every function that handles its argument's failure would spell out the pairing of [effects.paired-row-variables](../12-effects.md#effects.paired-row-variables).

Passing effects through is sound only if the function doesn't keep its argument: a kept function would run after the call that brought its effects has ended. So a parameter that passes effects through may only be called or passed on to another such parameter ([effects.no-escape](../12-effects.md#effects.no-escape)). A parameter that is kept is written `escaping`, with exactly the row its type writes ([effects.escaping-parameters](../12-effects.md#effects.escaping-parameters)). Two alternatives are rejected:

- **Inferring escape from the body.** Whether a parameter is kept decides what its row means to callers. Their typing would then depend on a body, and editing a body would check its callers again.
- **Knowing a kept parameter by a written row variable, with no keyword.** A parameter would be kept exactly when its row names a row variable. A constructor that keeps a callback with a fixed row, as `button(label: str, on_click: fn() / io)` does, couldn't be written.

`escaping` also tells a reader which arguments outlive the call. A closure literal's parameters need no such mark ([effects.closure-parameters](../12-effects.md#effects.closure-parameters)). A closure has no signature that callers check alone, so its parameters' rows are inferred from how the body uses it. Its type, an ordinary function type, has no place for the mark either.

## Raising and marking

`raise e` needs no mark, since it is explicit already ([effects.raise](../12-effects.md#effects.raise)). Every call that can raise sits inside a `try` ([effects.marking](../12-effects.md#effects.marking)). Every place where code can fail is then visible in the source, and marking it costs one word. This is Swift's `try`, which marks calls. Rust's `?` acts on a value instead.

Marking is lexical: a `try` outside a closure literal marks the calls inside it, so `try xs.map(|l| parse(l))` is enough. A separate `try` inside every closure is rejected as noise, since the outer `try` already shows the reader where the failure surfaces. A `try` that marks nothing is a warning ([effects.empty-try](../12-effects.md#effects.empty-try)), because a mark that means nothing teaches readers to skip marks.

A raise of the error type, which a row naming an unknown type produces, is accepted everywhere ([effects.error-type-raises](../12-effects.md#effects.error-type-raises)). The unknown name is already reported, and every diagnostic that the error type caused would repeat it.

**How raising is compiled.** None of this is part of the language. `raise` and `try` compile to tagged return values, with the error in a register, so the success path pays nothing and nothing unwinds the stack. A raise is a return that the caller checks.

## Handling errors

`catch` takes arms as `match` does ([effects.catch-syntax](../12-effects.md#effects.catch-syntax), [effects.catch](../12-effects.md#effects.catch)), so handling an error is matching on it, with exhaustiveness checked the same way. Marking is lexical, but handling is dynamic and typed ([effects.innermost-catch](../12-effects.md#effects.innermost-catch)). A raise goes to the innermost active `catch`. Every closure carries its raise in its type, so a closure that raises can't leave its handler without the type system seeing it.

A catch-all that neither raises nor uses its error gives a reason ([effects.catch-alls-need-reason](../12-effects.md#effects.catch-alls-need-reason)). Programmers and agents alike tend to catch every error and carry on. The reason makes that choice visible to a reviewer, as a reason on a lint suppression does. A reason on every catch-all that doesn't raise is rejected. A body that uses the error it binds shows, wraps or passes it on, which is what the reason guards against losing, so a reason there would restate the code. A reason on an arm that names a variant is an error ([effects.reasons-only-on-catch-alls](../12-effects.md#effects.reasons-only-on-catch-alls)), since such an arm drops nothing it didn't name.

## Failures that pass through

A raise that passes through a parameter belongs to the caller, and its type is the caller's to choose. A `catch` handles every raise that reaches it. So a `catch` around a call through a row variable could receive a raise of any type, which arms written for one type can't handle. The rules of this section make such a `catch` sound. Each rejects a program that would otherwise type-check and then hand a value of one type to code written for another.

Take `fn f<e>(escaping g: fn() / e) -> i64 / e`. Its body binds `let h: fn() / {raise<Box>, e} = g` and calls `h()` in the operand of a `catch` written for `Box`. A caller that passes `|| raise true` would make that `catch` receive a `bool`. [effects/unpaired_annotated_row.lt](../../conformance/effects/unpaired_annotated_row.lt) is the rejected program.

A `catch` may go through a row variable only when the row it calls holds `raise<E>` and the enclosing signature pairs the variable with `E` ([effects.catch-around-row-variables](../12-effects.md#effects.catch-around-row-variables), [effects.paired-row-variables](../12-effects.md#effects.paired-row-variables)). The pairing must be in the signature because callers check only the signature's rows. Each caller instantiates the variable, and a row of the signature that would then hold two `raise` labels is an error, so the variable adds no other error type. A row that the body forms, as the annotation on `h` above, pairs nothing, since no caller ever checks it. Three alternatives are rejected:

- **Rejecting the rows themselves,** so that a body could form a row holding `v` and `raise<E>` only when the signature pairs them. Such a row is harmless until a `catch` meets it, and outside a `catch` the body's own row must hold the effects anyway. The error belongs where the unhandled raise would arrive.
- **Forbidding every call through a row variable inside a `catch`.** It would reject `or_zero<E>(f: fn() -> i64 / raise<E>)`, which is sound: it catches the one error type that its signature pairs with the variable.
- **Checking the rows of a body at each call.** Callers would depend on the body of what they call.

A generic function can also hand its own row variable to a callee that pairs one ([effects.passing-to-paired-variables](../12-effects.md#effects.passing-to-paired-variables)). The row `{raise<E>, r}` has one `raise` label, so the callee's signature accepts it. The caller's own callers check only the caller's signature, though, and never learn that `r` is limited to `E`. So the enclosing signature must pair `r` with the same type, as `wrap(g: fn() -> i64 / raise<Box>)` does before it hands `g` to `Result.of`.

This suffices by induction on the order in which uses instantiate variables as the program runs. Each use that gives a paired variable a row variable is checked the same way. The chain ends at a use that gives a row with no variable, which the single `raise` label limits to `E`. The induction runs over uses, because a function value keeps the instantiation of the use that made it, wherever it is called later. So the rule applies inside closure literals too.

The simpler alternative is to reject any instantiation of a paired variable with a row variable. Generic code then couldn't pass a callback on to `Result.of` even when its own signature names the error type, which is sound. Inferring the pairing from the body is rejected because callers would depend on bodies. Tagging each raise with its type and checking at run time is rejected because it adds a cost to every raise that no correct program needs. The error of [effects.passing-to-paired-variables](../12-effects.md#effects.passing-to-paired-variables) has a code of its own, E0507, since it isn't about a `catch`. A use that E0506 already reports gets no second error ([effects.passing-reports](../12-effects.md#effects.passing-reports)): pairing the variable in the enclosing signature fixes both.

A paired variable may be given only the paired error type ([effects.what-paired-variable-may-raise](../12-effects.md#effects.what-paired-variable-may-raise)), even when no argument's type holds the row that would raise two types. The callee's own row would hold them once instantiated. The Lean model in `formal/` states the pairing rules as part of a program's typing, and proves the typing without them unsound.

## Failure as data

`Result` stores failure as a value that can be kept in a list or a field and looked at later ([effects.result](../12-effects.md#effects.result)). `try` never unwraps one. If it did, `try f()` would be ambiguous whenever `f` both raises and returns a `Result`. Converting between the two forms is one call either way, `get` and `Result.of`.

## Panics

A raise goes to a caller, which can handle it. A panic ends the program, and no construct catches it ([effects.panic-kinds](../12-effects.md#effects.panic-kinds)). Every panic has a kind, so a test can expect one and a reader of the report knows what went wrong.

`without panic` rules out the operations that panic, in the code's own body and in everything it calls ([effects.without-panic](../12-effects.md#effects.without-panic)). Overflow doesn't count against it ([effects.overflow-effect](../12-effects.md#effects.overflow-effect), [effects.without-overflow](../12-effects.md#effects.without-overflow)). Counting it would make every arithmetic operation in limited code need `checked_add` or a wrapping operator, and `without overflow` gives the stricter promise to code that wants it. `deadlock` doesn't count either, since every `when` whose block calls a function value could reach it. `without locks` is the promise that rules it out.

Every read of a map index adds `panic`, even on a map with a default ([effects.panicking-operations](../12-effects.md#effects.panicking-operations)), because whether a map has a default is known only at run time. A separate map type for maps with a default would keep `m[k]` on them out of the `panic` effect, at the cost of a second map type. Code limited by `without panic` uses `m.get(k)` instead. Division by a literal other than zero, and an index or a key that verification proves, add nothing, so ordinary limited code needs no rewriting for them.

## User-defined effects

Many functions need something whose implementation belongs to their caller. Examples are prices from a database in the program and from a table in a test, a log printed or kept in a list, and a source of time. Passing each as a parameter threads it through every call between the code that has it and the code that needs it. An effect declares operations, a function that performs them says so in its row, and the caller installs a handler for the length of a block ([handlers.declaring-effect](../12-effects.md#handlers.declaring-effect), [handlers.performing-operation](../12-effects.md#handlers.performing-operation)). Koka, Effekt and OCaml 5 work the same way. An effect is a row element like any other ([handlers.rows-pass-effects-on](../12-effects.md#handlers.rows-pass-effects-on)). So a function passed to `map` performs its caller's effects as it performs `io`, and no new colour of function appears.

An effect has at least one operation. Nothing could perform an effect with none, so a row that named it would mean nothing.

Operations take no generics. A generic operation, as `fn spawn<T>(…)`, would need its handler's implementation checked with rigid types, and no effect needs one. Operations take their arguments by value ([handlers.no-inout-parameter](../12-effects.md#handlers.no-inout-parameter)). A handler that takes control may run after `resume`, when the access that would lend a place has ended. An `inout` parameter written then would reach nothing in a copy-in, copy-out implementation, and the caller's place in one that writes in place. Two alternatives are rejected:

- **An `inout` parameter whose access lasts until `resume`.** It would need a third duration, ending with the `with`, for a handler that never resumes. A returned value already covers that case.
- **`inout` parameters only on operations of handlers that resume at once.** A fact of the handler would decide a declaration of the effect, which doesn't know its handlers.

Handling capabilities such as `clock` or `fs` as effects is not part of this design: handling them would change what `io` means in every signature.

## Handlers

A handler is a value that implements each operation ([handlers.handler-literals](../12-effects.md#handlers.handler-literals), [handlers.handler-types](../12-effects.md#handlers.handler-types)), and `with` installs it for a block ([handlers.with](../12-effects.md#handlers.with)). A function that performs `Prices` is tested with a table of prices and run with a database, with no parameter threaded through the calls between.

Handlers resume at most once ([handlers.resuming](../12-effects.md#handlers.resuming), [handlers.resume-at-most-once](../12-effects.md#handlers.resume-at-most-once)), as OCaml 5's do. Multi-shot continuations, which resume more than once, are rejected. A continuation resumed twice runs the same code with the same bindings twice, so two futures of one computation would share values that the value model gives one owner. Every runtime would also need to copy stacks.

The common handler resumes at once with its value, so that form needs no keyword, and `-> R` marks the handlers that take control. A keyword on every resumption, as `resume price(sku)` in every handler, is rejected because it would only restate the common case. Telling the two kinds apart by whether a body names `resume` is rejected too. A handler that only ends its `with`, as one that turns a failure into a default, names no `resume`, and would resume instead.

A `with` handles every performance that reaches it, as a `catch` handles every raise. So the pairing that makes a `catch` sound makes a `with` sound ([handlers.with-pairing](../12-effects.md#handlers.with-pairing)). Handling effects by name in lexical scope, as Effekt's capabilities do, would avoid accidental handling altogether. It is rejected for this tier. A function would take a capability parameter for each effect, which rows already say, and functions passed as arguments couldn't perform their caller's effects without one. No effect reaches `main` ([handlers.no-effect-reaches-main](../12-effects.md#handlers.no-effect-reaches-main)), so every performance in a program runs under a handler.

A handler's bodies run with the handlers outside its `with` ([handlers.with](../12-effects.md#handlers.with)), so a body that performs its own effect reaches the next handler out, as a handler that delegates wants. So the `with` performs what the bodies perform, the effects of their operations' rows included, and a handler installed between the performance and the `with` never sees them. Effekt's bidirectional effects, whose operations' rows reach the handlers at the performance, are rejected: a body would run under two sets of handlers, those at the performance for its operation's row and those outside the `with` for everything else. For the same reason, the rest of a block that a body resumes runs under the handlers around the performance, never under one that the body installs around `resume` ([handlers.resuming](../12-effects.md#handlers.resuming)), where Koka would run it under the body's.

**How handlers are compiled.** None of this is part of the language. A handler is passed as evidence: a record of its implementations, held in a vector that each `with` extends and indexed by effect, as in Xie and Leijen's evidence passing. A handler written without `-> R` is called directly, so a performance is an indirect call. A body that ends the `with` without resuming returns a tagged value up to the `with`, as a raise does. A body that resumes and goes on runs the rest of the block on a stack of its own, which the runtime switches to and back from. The body resumes once, so no stack is copied.

## Calls that a handler ends

A handler that takes control may end its `with` without resuming. Every call between the performance and the `with` then ends early, some of them in the middle of an `inout` access. Such a call ends as a raise ends it ([handlers.call-that-handler-ends](../12-effects.md#handlers.call-that-handler-ends)): every `inout` argument keeps what the callee wrote before the performance. One rule then covers every early end, with no rule on handlers and no mark on effects. Two alternatives are rejected:

- **Requiring an operation performed during an `inout` access to resume exactly once.** The code that performs doesn't know its handler. So every operation would need a mark saying whether a handler may end the `with`. The rule would also forbid handlers that the raise semantics already explain.
- **Rolling `inout` arguments back.** Exact rollback would copy every `inout` argument on entry to every call, a hidden cost, as it would be for a raise.

A handler's body sees only values and copies ([handlers.when-place-is-seen](../12-effects.md#handlers.when-place-is-seen), [handlers.resuming-keeps-exclusivity](../12-effects.md#handlers.resuming-keeps-exclusivity)). So when an ended call's `inout` arguments are written back can't be observed, and no access of the body overlaps one of the code it suspends. An operation reads like a call of a function whose arguments are `let`. Its handler can't be told from a function called where the operation is performed, except for when it runs.

**How ended calls are implemented.** The compiler writes `inout` arguments in place, so it does nothing more: a body that ends its `with` returns a tagged value up to it. The reference interpreter copies `inout` arguments in and out, and writes them back as the frames between the performance and the `with` are unwound. The Lean model shows that the two give the same store (`formal/Stilt/Interactions/Ended.lean`). It also shows that a handler's body, given values and copies, writes no place of the code it suspends (`formal/Stilt/Interactions/Resumed.lean`).
