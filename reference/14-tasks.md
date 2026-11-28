# 14. Tasks, shared state and parallelism

A task is a function that runs beside the code that started it, through the effect `async`. This chapter defines tasks and the sequential run that gives every program with tasks its one meaning, then scopes of tasks that may fail. It then defines shared values, which only `when` reaches, and the fact `locks`. It ends with the parallel calls of `std.par`, which perform nothing, and with the cycles that shared values can form, and how they are freed. Everything here belongs to the advanced tier except `std.par`, which is core.

[Effects and handlers](12-effects.md) defines rows and handlers. [Modes and exclusivity](13-modes.md) defines the modes that say which values may reach another task. [Inferred facts and limits](15-facts.md) defines the facts that tasks, `when` and parallel calls add.

## Tasks

<a id="tasks.async"></a>
`async` is an effect and a keyword ([lexical.reserved-words](02-lexical.md#lexical.reserved-words)). It is written in a row as `io` is, as in `/ {io, async}`. The functions of `std.task` that start and wait for tasks perform it ([tasks.std-task](#tasks.std-task)). Its handlers are the values that `std.task` gives, so a handler literal of `async` is E0511 ([handlers.handler-literals](12-effects.md#handlers.handler-literals)).

Otherwise `async` is an effect as a user-defined one is. Rows and row variables pass it on ([handlers.rows-pass-effects-on](12-effects.md#handlers.rows-pass-effects-on)), and a `with` of one of its handlers handles it ([handlers.with](12-effects.md#handlers.with)). It is part of the advanced tier ([tasks.advanced-tier](#tasks.advanced-tier)).

Tests: [tasks/async_in_core.lt](../conformance/tasks/async_in_core.lt), [tasks/errors.lt](../conformance/tasks/errors.lt), [tasks/rows.lt](../conformance/tasks/rows.lt), [tasks/tasks.lt](../conformance/tasks/tasks.lt), [threads/handlers.lt](../conformance/threads/handlers.lt).

<a id="tasks.std-task"></a>
The module `std.task` declares:

- `pub type Task<T> = ?`, a task's handle, which implements no trait;
- `pub fn spawn<T>(escaping f: fn() -> T / {io, async}) -> Task<T> / async`, which starts a task that runs `f` and gives its handle;
- `pub fn await(self) -> T / async`, a method of `Task<T>`, written `t.await()`, which waits for the task to end and gives the value it ended with, as often as it is called;
- `pub fn threads() -> handler async` and `pub fn sequential() -> handler async`, the two handlers of `async`.

`await` is a keyword, which the grammar reads as a member's name after `.` ([syntax.effect-forms](03-syntax.md#syntax.effect-forms)). This is the one declaration that a keyword names, and only `std` may write it. `std.task` declares scopes too ([tasks.scopes](#tasks.scopes)).

Tests: [tasks/rows.lt](../conformance/tasks/rows.lt), [tasks/tasks.lt](../conformance/tasks/tasks.lt), [threads/handles.lt](../conformance/threads/handles.lt).

<a id="tasks.task-functions"></a>
A task's function may perform `io` and `async`, so a task may print and start tasks. It raises nothing, so a task that can fail gives a `Result` ([effects.result](12-effects.md#effects.result)) or runs in a scope ([tasks.scopes](#tasks.scopes)). It performs no user-defined effect.

A closure literal given to `spawn` is checked against the parameter's type ([types.expected-types](07-types.md#types.expected-types)). So a `raise` or a performance in its body is E0502 ([effects.inference](12-effects.md#effects.inference)). A task's function must also be `portable` ([shared.tasks-and-modes](#shared.tasks-and-modes)).

Tests: [tasks/errors.lt](../conformance/tasks/errors.lt), [tasks/rows.lt](../conformance/tasks/rows.lt).

<a id="tasks.values-in-tasks"></a>
A task's function captures values as any closure literal does, by copy when it is made ([expressions.capture](08-expressions.md#expressions.capture)). So a task and the code that started it share no place: what one writes, the other doesn't see. Values that several tasks change live in a `Shared<T>` ([shared.std-sync](#shared.std-sync)).

Tests: [tasks/tasks.lt](../conformance/tasks/tasks.lt), [threads/handles.lt](../conformance/threads/handles.lt).

<a id="tasks.with-waits"></a>
A `with` of an `async` handler ends once every task started under it has ended, so no task outlives the block that started it. A task's handle that a statement drops is no unused value ([expressions.unused-values](08-expressions.md#expressions.unused-values)). The task still runs, and the `with` waits for it.

Tests: [tasks/output.lt](../conformance/tasks/output.lt), [threads/handlers.lt](../conformance/threads/handlers.lt), [threads/interleaved.lt](../conformance/threads/interleaved.lt).

<a id="tasks.advanced-tier"></a>
A module is in the advanced tier ([program.module-tier](04-programs.md#program.module-tier)) when it writes `async` in a row or a type, names `std.task` or `std.sync`, or writes `when`. So is every program that [shared.names-that-may-be-one-place](#shared.names-that-may-be-one-place) and [shared.when-on-value-already-held](#shared.when-on-value-already-held) affect. A module that names `std.par` stays in its tier ([par.core-tier](#par.core-tier)).

Checked by: the facts suite, whose `tests/facts/tasks.lt` and `tests/facts/shared.lt` carry `//~ tier: advanced`, which `just facts` checks (`compiler/stilt-cli/tests/facts.rs`); and every conformance test of `tasks/`, `shared/`, `held/` and `threads/`, each of which carries `//~ tier: advanced`.

## The sequential run

<a id="tasks.sequential-run"></a>
A program's meaning is its run under `task.sequential()`. In this run, `spawn` runs the task's function to its end before it returns, and `await` gives the value the task ended with. `main` and tests run under `task.sequential()` when no `with` installs another handler of `async`. So the row of `main` and a test's body may hold `async` ([program.main](04-programs.md#program.main), [program.test-declarations](04-programs.md#program.test-declarations)), and the row of a doc example must not.

Tests: [tasks/output.lt](../conformance/tasks/output.lt), [tasks/rows.lt](../conformance/tasks/rows.lt), [tasks/tasks.lt](../conformance/tasks/tasks.lt), [threads/exit.lt](../conformance/threads/exit.lt), [threads/handlers.lt](../conformance/threads/handlers.lt), [threads/handles.lt](../conformance/threads/handles.lt), [threads/interleaved.lt](../conformance/threads/interleaved.lt), [threads/panic_first.lt](../conformance/threads/panic_first.lt), [threads/reads.lt](../conformance/threads/reads.lt), [threads/testing.lt](../conformance/threads/testing.lt).

<a id="tasks.same-output-under-every-handler"></a>
Under `task.threads()`, a task runs on a thread of its own, at the same time as the code that started it. Every program writes to stdout and stderr, reads stdin and ends with the status that its sequential run gives:

- What a task writes appears where the sequential run writes it, before what the code that started it writes after the `spawn`.
- A read waits until every write that the sequential run makes before it is out.
- A panic or an `exit` in a task ends the program where the sequential run would, with the output written before that point and nothing after it ([program.exit-statuses](04-programs.md#program.exit-statuses)).

So a program prints the same under every handler of `async`.

Tests: [tasks/output.lt](../conformance/tasks/output.lt), [tasks/panic.lt](../conformance/tasks/panic.lt), [tasks/tasks.lt](../conformance/tasks/tasks.lt), [threads/exit.lt](../conformance/threads/exit.lt), [threads/handlers.lt](../conformance/threads/handlers.lt), [threads/interleaved.lt](../conformance/threads/interleaved.lt), [threads/panic_first.lt](../conformance/threads/panic_first.lt), [threads/reads.lt](../conformance/threads/reads.lt), [threads/testing.lt](../conformance/threads/testing.lt).

<a id="tasks.unordered-io"></a>
Under `task.threads()`, tasks reach files, the network, the clock, the environment and randomness at the same time, in an order that isn't part of the program's meaning. A program whose output depends on how two tasks' uses of them interleave has no single meaning under `task.threads()`. Its sequential run is the reference.

Checked by: no test, since what isn't part of a program's meaning is what no program can observe.

## Scopes

<a id="tasks.scopes"></a>
`std.task` declares `pub type Scope<E> = ?`, a scope of tasks that may raise `E`, and two functions:

- `pub fn scope<T, E>(f: fn(Scope<E>) -> T / {io, async, raise<E>}) -> T / {io, async, raise<E>}`, which runs `f` with a new scope and ends once every task started in it has ended;
- `pub fn spawn<U>(self, escaping f: fn() -> U / {io, async, raise<E>}) -> Task<U> / {async, raise<E>}`, a method of `Scope<E>`, written `s.spawn(f)`, which starts a task of the scope that may raise `E`.

Tests: [shared/scopes.lt](../conformance/shared/scopes.lt), [threads/scope_await.lt](../conformance/threads/scope_await.lt).

<a id="tasks.scope-failure"></a>
In the sequential run, `s.spawn` runs the task to its end, and a task that raises raises at `s.spawn`. So the call is marked with `try` ([effects.marking](12-effects.md#effects.marking)), and the raise leaves the scope as any raise does, unless the scope's function catches it.

Under `task.threads()`, the scope gives the same result:

- The first raise in the sequential order is the one the scope raises.
- Every task of the scope after it in that order is cancelled.
- Nothing that those tasks or the scope's function would write to stdout or stderr after that point appears.

A cancelled task, and the scope's function past the raise that cuts it, is code that the sequential run never reaches. Its panic or `exit` ends nothing. What it reached of files, the network, the clock, the environment or randomness before it was cancelled isn't undone ([tasks.unordered-io](#tasks.unordered-io)). The scope ends once every task that the sequential run reaches has ended, and waits for no cancelled task.

Tests: [shared/scopes.lt](../conformance/shared/scopes.lt), [threads/cancelled_loop.lt](../conformance/threads/cancelled_loop.lt), [threads/cancelled_panic.lt](../conformance/threads/cancelled_panic.lt), [threads/cut_function.lt](../conformance/threads/cut_function.lt), [threads/scope_await.lt](../conformance/threads/scope_await.lt), [threads/scope_when.lt](../conformance/threads/scope_when.lt).

<a id="tasks.scope-that-escapes"></a>
A binding of type `Scope<E>` is used only as the receiver of `spawn` or as an argument given to a parameter of type `Scope<E>`. Any other use, a capture in a task's function included, is a scope that escapes (E0434), at the first such use in source order. So a scope never outlives the call of `task.scope` that made it. The check is the one for a non-escaping parameter ([effects.no-escape](12-effects.md#effects.no-escape)), with a parameter of type `Scope<E>` among the places a scope may go.

Tests: [shared/scope_escapes.lt](../conformance/shared/scope_escapes.lt).

## Shared values

<a id="shared.std-sync"></a>
The module `std.sync` declares `pub type Shared<T> = ?`, a handle on a value with one identity. It also declares `Shared.new(value: T) -> Shared<T>`, which makes a handle that holds `value`. A handle is copied as any value is, and every copy reaches the same value ([values.shared](05-values.md#values.shared)).

`Shared<T>` implements no trait, and its value is reached only inside a `when` that names the handle ([shared.when](#shared.when)). A field access, an index and a method call on a `Shared<T>` are errors, as on a type without them. A field is E0313, an index E0317 and a method E0314. The value given to `Shared.new` must be `portable`, so a view put in one is E0432 ([shared.tasks-and-modes](#shared.tasks-and-modes)).

Tests: [shared/errors.lt](../conformance/shared/errors.lt), [shared/transfers.lt](../conformance/shared/transfers.lt).

<a id="shared.when"></a>
`when a, b { block }` (a `primary`, [syntax.expressions](03-syntax.md#syntax.expressions)) names one or more bindings, locals or parameters, whose types are `Shared<T>`. Any other name or type, and a name given twice, is a `when` on something that isn't shared (E0433).

The `when` waits until it holds every value that its handles reach, then runs `block`, and then releases the values. In `block`, each name stands for the place of its handle's value, of type `T`, readable and writable as a `var` is ([modes.what-can-be-modified](13-modes.md#modes.what-can-be-modified)). Each value keeps what its place holds when the block ends, however it ends. The `when`'s value is the block's.

Inside the block, a name stands for a `T`, not a handle, so a `when` there that names it is E0433. Two names whose handles reach one value are one place: a write through one is read through the other ([shared.names-that-may-be-one-place](#shared.names-that-may-be-one-place)).

Tests: [modes/handles.lt](../conformance/modes/handles.lt), [modes/shared_writes_in_when.lt](../conformance/modes/shared_writes_in_when.lt), [ported/effekt_multihandler.lt](../conformance/ported/effekt_multihandler.lt), [ported/effekt_nim.lt](../conformance/ported/effekt_nim.lt), [ported/effekt_stream_pull.lt](../conformance/ported/effekt_stream_pull.lt), [ported/koka_linear_state.lt](../conformance/ported/koka_linear_state.lt), [shared/errors.lt](../conformance/shared/errors.lt), [shared/transfers.lt](../conformance/shared/transfers.lt), [shared/views_in_when.lt](../conformance/shared/views_in_when.lt), [shared/when_left_by_handler.lt](../conformance/shared/when_left_by_handler.lt), [threads/scope_when.lt](../conformance/threads/scope_when.lt).

<a id="shared.when-order"></a>
The `when` blocks that reach one value run one at a time, in the order in which the sequential run reaches them ([tasks.sequential-run](#tasks.sequential-run)). So a program that shares values prints the same under every handler of `async`. A `when` holds all its values at once, so no two `when`s wait on each other, and none deadlocks.

Tests: [shared/order.lt](../conformance/shared/order.lt), [shared/transfers.lt](../conformance/shared/transfers.lt), [threads/interleaved.lt](../conformance/threads/interleaved.lt), [threads/scope_when.lt](../conformance/threads/scope_when.lt).

<a id="shared.tasks-and-modes"></a>
A value that reaches another task must be `portable` ([modes.fixed-values](13-modes.md#modes.fixed-values), [modes.demands](13-modes.md#modes.demands)). Such a value is the value given to `Shared.new`, or a task's function, given to `task.spawn` or to `s.spawn`.

A `fixed` value given to `Shared.new`, as a view is, is a value that can't reach another task (E0432), at the value. So is a task's function that captures a `fixed` binding, at the capture. Each has one note, at the binding that gave it the mode ([modes.diagnostic-shape](13-modes.md#modes.diagnostic-shape)). A `Shared<T>` is `portable` and `contended` ([modes.contended-values](13-modes.md#modes.contended-values)), so a task captures handles freely.

Tests: [par/demanded_arguments.lt](../conformance/par/demanded_arguments.lt), [par/held_through_declarations_accepted.lt](../conformance/par/held_through_declarations_accepted.lt), [shared/errors.lt](../conformance/shared/errors.lt).

## Holding shared values

<a id="shared.locks"></a>
Running a `when` gives a function the inferred fact `locks`, which is inferred as the implicit effects are ([facts.inference](15-facts.md#facts.inference)). A `when` is a site of it, and so is a call of a function that has it, or a use of one as a value. A call through a function value adds nothing ([facts.calls-through-function-values](15-facts.md#facts.calls-through-function-values)), and a closure literal's body is part of the function that writes it.

A `when` whose block holds a site of `locks` is a `when` inside a `when` (E0430), at the site. `locks` is a limit of a `without` clause and a contextual keyword ([facts.without](15-facts.md#facts.without), [facts.spelling](15-facts.md#facts.spelling)). So `without locks` promises that the code holds no `Shared<T>`, with E0204 at each site. `stilt show` prints `locks` in a function's bracket of facts ([facts.visibility](15-facts.md#facts.visibility)).

Tests: [shared/errors.lt](../conformance/shared/errors.lt).

Checked by: also the facts suite, whose `tests/facts/shared.lt` gives `LOCKS` at each site, which `just facts` checks.

<a id="shared.names-that-may-be-one-place"></a>
For the law of exclusivity ([modes.law](13-modes.md#modes.law)), the names of one `when` whose values have the same type are one binding. An access to a place rooted in one overlaps an access to the same place rooted in another, as two accesses rooted in one name do. Take `a` and `b`, the names of one `when` of `Shared<Account>` values. Then `both(inout a.balance, inout b.balance)` is E0402 ([modes.overlapping-inout](13-modes.md#modes.overlapping-inout)), as `both(inout a.balance, inout a.balance)` is, while `both(inout a.balance, inout b.fee)` is accepted.

Every other rule of the law applies the same way. Changing `b.items` in a `for` over `a.items` is E0404 ([modes.change-while-iterating](13-modes.md#modes.change-while-iterating)). A view of a place rooted in one name, while a place rooted in another is changed or reached, is E0423 or E0429 ([views.change-while-viewed](13-modes.md#views.change-while-viewed), [projections.reaching-written-source](13-modes.md#projections.reaching-written-source)). Names whose values have different types never reach one value, and are checked as separate bindings.

Tests: [held/fields.lt](../conformance/held/fields.lt), [held/names.lt](../conformance/held/names.lt), [verification/counting_loops_held_rejected.lt](../conformance/verification/counting_loops_held_rejected.lt), [verification/guards_held_rejected.lt](../conformance/verification/guards_held_rejected.lt), [verification/order_effects_rejected.lt](../conformance/verification/order_effects_rejected.lt).

<a id="shared.when-on-value-already-held"></a>
A `when` that names a value held by a `when` whose block hasn't ended panics with the kind `deadlock` ([effects.panic-kinds](12-effects.md#effects.panic-kinds)), at the `when`, before it holds anything. E0430 rejects every such `when` that the code shows ([shared.locks](#shared.locks)). So in the sequential run, one is reached only through a call of a function value or through a handler's body. A `when` that runs while a `Lazy` computes its value panics the same way ([polymorphism.lazy-waits-for-nothing](07-types.md#polymorphism.lazy-waits-for-nothing)).

The kind `deadlock` doesn't count against `without panic`, as `overflow` doesn't: `without locks` is the promise that rules it out. Under `task.threads()`, the program panics where the sequential run does ([tasks.same-output-under-every-handler](#tasks.same-output-under-every-handler)). So a task that a `when`'s block starts, which the sequential run runs inside the block, panics in the same place.

Tests: [held/deadlock.lt](../conformance/held/deadlock.lt), [held/deadlock_handler.lt](../conformance/held/deadlock_handler.lt), [held/deadlock_task_sequential.lt](../conformance/held/deadlock_task_sequential.lt), [held/deadlock_task_threads.lt](../conformance/held/deadlock_task_threads.lt), [held/other_value.lt](../conformance/held/other_value.lt), [polymorphism/lazy_deadlock.lt](../conformance/polymorphism/lazy_deadlock.lt), [polymorphism/lazy_deadlock_par.lt](../conformance/polymorphism/lazy_deadlock_par.lt), [polymorphism/lazy_reaches_itself.lt](../conformance/polymorphism/lazy_reaches_itself.lt).

## Continuations

<a id="tasks.continuations-stay-in-task"></a>
A performance of an operation, the body of the handler that takes it, and the `resume` that continues it run in one task: the one that runs the `with`. Three rules give this:

- `resume` is in no closure literal ([handlers.resume-at-most-once](12-effects.md#handlers.resume-at-most-once)), so no task's function holds one.
- A task's function performs no user-defined effect ([tasks.task-functions](#tasks.task-functions)), so a performance in a task is handled by a `with` in that task.
- The functions given to `std.par` perform nothing ([par.what-runs-in-parallel](#par.what-runs-in-parallel)).

So a handler's captures, its bodies' stacks and the frames of a continuation stay on one thread.

Tests: [continuations/handlers_in_tasks.lt](../conformance/continuations/handlers_in_tasks.lt), [continuations/performed_in_task.lt](../conformance/continuations/performed_in_task.lt), [continuations/resume_in_task.lt](../conformance/continuations/resume_in_task.lt).

## Parallel calls

<a id="par.std-par"></a>
The module `std.par` declares four native functions ([declarations.native-items](10-declarations.md#declarations.native-items)), and names no other module:

- `pub fn map<T, U>(xs: List<T>, escaping f: fn(T) -> U) -> List<U>`, the list of `f` of each element, in order;
- `pub fn each<T>(inout xs: List<T>, escaping f: fn(inout T))`, which calls `f` on each element of `xs` in place;
- `pub fn both<A, B>(escaping f: fn() -> A, escaping g: fn() -> B) -> (A, B)`, the pair of their values;
- `pub fn fold<T>(xs: List<T>, empty: T, escaping f: fn(T, T) -> T) -> T`, which combines the elements in the tree of [par.fold-tree](#par.fold-tree), and gives `empty` for an empty list.

Tests: [par/functions.lt](../conformance/par/functions.lt).

<a id="par.what-runs-in-parallel"></a>
Each parameter of a function of `std.par` that takes a function is `escaping` with no row ([effects.escaping-parameters](12-effects.md#effects.escaping-parameters)). So its argument performs no effect, `io` and `raise` included, and the call passes none through. A closure literal whose body prints or raises is E0502 there ([effects.inference](12-effects.md#effects.inference)), and a named function whose row isn't empty is a type mismatch (E0311).

The argument must also be `calm` and `portable` ([modes.demands](13-modes.md#modes.demands)). One that reaches a `Shared<T>` or a view is a closure that can't run in parallel (E0431), at the argument. The error has one note, at the binding that gave it the mode ([modes.diagnostic-shape](13-modes.md#modes.diagnostic-shape)). So no program can tell how many threads ran a call.

Tests: [par/demanded_arguments.lt](../conformance/par/demanded_arguments.lt), [par/function_types_hold_nothing.lt](../conformance/par/function_types_hold_nothing.lt), [par/held_through_declarations.lt](../conformance/par/held_through_declarations.lt), [par/held_through_declarations_accepted.lt](../conformance/par/held_through_declarations_accepted.lt), [par/rows.lt](../conformance/par/rows.lt).

<a id="par.sequential-meaning"></a>
Each function of `std.par` means its sequential run: `map` and `each` call `f` on the elements from the first to the last, and `both` calls `f`, then `g`.

Tests: [par/functions.lt](../conformance/par/functions.lt).

<a id="par.fold-tree"></a>
`fold` combines a list of `n` elements in a balanced tree that depends on `n` alone. One element is itself. A longer list is its first `⌊n/2⌋` elements folded, combined by `f` with the rest folded. So `fold([a, b, c, d], e, f)` is `f(f(a, b), f(c, d))`, and `fold([a, b, c], e, f)` is `f(a, f(b, c))`. A fold of floats gives the same bits on every machine and with every number of threads ([numbers.ieee-754](06-numbers.md#numbers.ieee-754)), though it may differ from a loop from left to right.

Tests: [par/floats.lt](../conformance/par/floats.lt), [par/functions.lt](../conformance/par/functions.lt).

<a id="par.panics"></a>
A panic in a call of `f` or `g` is the program's panic, as in the sequential run. When several calls panic, the program reports the panic of the first in the order of [par.sequential-meaning](#par.sequential-meaning) and [par.fold-tree](#par.fold-tree), and none of the others. It ends with what it wrote before the call, and nothing else.

Tests: [par/panics.lt](../conformance/par/panics.lt).

<a id="par.writes-in-place"></a>
`each` writes into the storage of `xs`, made unique first when it is shared. So another binding that shares the list keeps its own value ([values.independent-copies](05-values.md#values.independent-copies)). Each call of `f` writes one element. A list split by `view.split` into writable parts ([projections.writable-views](13-modes.md#projections.writable-views)) is written in parallel by calling `par.both` with a function on each part.

Tests: [par/functions.lt](../conformance/par/functions.lt).

<a id="par.core-tier"></a>
`std.par` belongs to the core tier, as the rest of the library does: a module that names it stays in its tier. Every binding of a core module is `calm` and `portable` ([modes.fixed-values](13-modes.md#modes.fixed-values), [modes.contended-values](13-modes.md#modes.contended-values)). So E0431 arises only where a value of the advanced tier is reached.

Checked by: the facts suite, whose `tests/facts/parallel.lt` names `std.par` and carries `//~ tier: core`, which `just facts` checks.

## Facts of tasks, shared values and parallel calls

<a id="tasks.implicit-effects-and-capabilities"></a>
A call of `task.spawn` or `s.spawn` is a call through a stored function value ([facts.calls-through-function-values](15-facts.md#facts.calls-through-function-values)). It is a site of `div` ([facts.div](15-facts.md#facts.div)), it allocates the task, as every native of `std.task` does ([facts.native-allocation](15-facts.md#facts.native-allocation)), and the body of the closure literal it is given adds its own sites where it is written.

Both functions have the capability `spawn` ([facts.capability-natives](15-facts.md#facts.capability-natives)), which they reach through `async`, not `io` ([facts.io-and-capabilities](15-facts.md#facts.io-and-capabilities)). So a function that starts tasks that only compute performs no `io`. A `when` adds `locks` ([shared.locks](#shared.locks)), and no other fact of its own.

Tests: [implicit/allocating_natives.lt](../conformance/implicit/allocating_natives.lt), [tasks/spawn_without_div.lt](../conformance/tasks/spawn_without_div.lt).

Checked by: the facts suite, whose `tests/facts/tasks.lt` and `tests/facts/shared.lt` give `DIV` and `SPAWN` at each `spawn` and `LOCKS` at each `when`, which `just facts` checks.

<a id="par.implicit-effects-and-capabilities"></a>
A call of a function of `std.par` has the implicit effects of its arguments, counted where a closure literal is written or a function named ([facts.inference](15-facts.md#facts.inference)). It also has `alloc`, as every native of `std.par` does ([facts.native-allocation](15-facts.md#facts.native-allocation)). It has no capability, so it doesn't need `spawn`.

Tests: [implicit/allocating_natives.lt](../conformance/implicit/allocating_natives.lt).

Checked by: the facts suite, whose `tests/facts/parallel.lt` gives each call the facts of its closure, which `just facts` checks.

<a id="par.atomic-sites"></a>
`stilt show` prints, at the line of each operation that may make reference counts atomic, what it marks:

- a call of `par.map`, `par.each` or `par.fold`, which marks its closure and the elements of its list that something else references too, as `[a, a]` reaches `a`;
- a call of `par.both`, which marks its second closure;
- a call of `Shared.new`, which marks its value;
- a `when`, which marks what it leaves in the values it holds;
- a call of `task.spawn`, `s.spawn` or `task.scope` whose function may reach another task's handle, which marks the handles it reaches and their tasks' values. Such a function is a closure literal that captures a value whose type holds a `Task<T>` or a function type, or any other function value.

A closure literal's operations are its writer's, as for the implicit effects. The fact is printed at its line, not after the signature, and is no part of a package's API ([versions.facts-in-api](21-versions.md#versions.facts-in-api)). A call over a few elements runs on the calling thread alone and marks nothing. `show` can't know which calls do, so it prints every such call as one that may.

Checked by: the facts suite, whose `tests/facts/parallel.lt`, `tests/facts/shared.lt` and `tests/facts/tasks.lt` give `ATOMIC` at these lines and nowhere else, which `just facts` checks, and the toolchain's tests of `stilt show` (`compiler/stilt-cli/tests/show.rs`).

## Cycles

<a id="cycles.through-shared-values"></a>
A value reaches itself only through a `Shared<T>`. A `when` makes a **cycle** when it leaves in a handle's value something that reaches the same handle. That something reaches the handle through other values and handles, a closure that captures one, or a task's handle whose value holds one. No other value is ever in a cycle ([values.independent-copies](05-values.md#values.independent-copies)).

Tests: [cycles/closure.lt](../conformance/cycles/closure.lt), [cycles/one_handle.lt](../conformance/cycles/one_handle.lt), [cycles/task_value.lt](../conformance/cycles/task_value.lt), [cycles/threads.lt](../conformance/cycles/threads.lt), [cycles/two_handles.lt](../conformance/cycles/two_handles.lt), [polymorphism/lazy_reaches_itself.lt](../conformance/polymorphism/lazy_reaches_itself.lt).

<a id="cycles.freeing"></a>
A value is freed once nothing that the running program holds reaches it any more. What the program holds is a binding, a parameter, a frame's temporary, a constant, a running task, or a handle's value that something it holds reaches. Everything that only that value reaches is freed with it, the values of cycles among them.

So every value a program made is freed by the time it ends, unless one of these holds:

- it ends by a panic, an `exit`, a stack overflow or running out of memory;
- it ends while a thread of code that the sequential run never reaches holds values ([tasks.scope-failure](#tasks.scope-failure)).

A program that lets cycles go runs out of memory only when what it still reaches doesn't fit in the heap ([program.exit-statuses](04-programs.md#program.exit-statuses)).

Tests: [cycles/closure.lt](../conformance/cycles/closure.lt), [cycles/kept.lt](../conformance/cycles/kept.lt), [cycles/one_handle.lt](../conformance/cycles/one_handle.lt), [cycles/task_value.lt](../conformance/cycles/task_value.lt), [cycles/threads.lt](../conformance/cycles/threads.lt), [cycles/two_handles.lt](../conformance/cycles/two_handles.lt).

Checked by: also the toolchain's tests of cycles (`compiler/stilt-cli/tests/cycles.rs`), in which a loop lets go of 2,000 cycles that each hold a list of 100,000 integers, 1.6 GB in all, and runs to its end within a heap that `STILT_HEAP` sets to 512 MiB, under `stilt run` and as a debug build, while the same loop keeping every cycle outgrows it and ends with status 134.

<a id="cycles.freeing-is-unseen"></a>
Freeing a value runs none of the program's code. A type has no destructor, and a task's handle that goes stops nothing: its task runs as the sequential run runs it. So when a value is freed, a cycle's or another's, changes nothing that a program prints, returns or reads. No program can ask whether a value was freed: there is no weak handle.

Checked by: no test, since when a value is freed is what no program can observe.

<a id="cycles.can-form-cycle"></a>
A declared type **can form a cycle** when one of its fields or variants holds a `Shared<U>` that can reach itself.

- **Holding.** A type holds itself and the types of its fields and variants. It holds the types of its elements and its type arguments, with a declared type's arguments put where its declaration places them. It also holds the `U` of a `Shared<U>` and of a `Task<U>`, and what each of those holds. A function type holds only itself: what its parameters and result name, a value of it takes or gives when it is called and holds none of.
- **Reaching itself.** A `Shared<U>` can reach itself when `U` holds one of these:
  - that same `Shared<U>`;
  - a function or handler type;
  - a type parameter, applied or not, or a pack;
  - a `Lazy<T>` ([polymorphism.lazy-values](07-types.md#polymorphism.lazy-values)).

`stilt show` writes ``// can form a cycle, through `f` `` at the end of such a type's first line. It names each field or variant through which the type can, in declaration order, with `,` between them and `and` before the last. The type's JSON record lists their names under `cycle`. The fact limits nothing, and is no part of the package's API ([versions.facts-in-api](21-versions.md#versions.facts-in-api)).

Checked by: the facts suite, whose `CYCLE` annotations in `tests/facts/cycles.lt` `just facts` checks, and the toolchain's tests of `stilt show --json` (`compiler/stilt-cli/tests/cycles.rs`).

<a id="cycles.check-at-exit"></a>
A debug build checks, after the program ends as [cycles.freeing](#cycles.freeing) says, that every value it made was freed. A value that wasn't is the toolchain's bug: the program prints `stilt: internal error: N objects were never freed` to stderr and ends with status 70. A release build doesn't check ([builds.release-builds](20-builds.md#builds.release-builds)).

Tests: [cycles/closure.lt](../conformance/cycles/closure.lt), [cycles/kept.lt](../conformance/cycles/kept.lt), [cycles/one_handle.lt](../conformance/cycles/one_handle.lt), [cycles/task_value.lt](../conformance/cycles/task_value.lt), [cycles/threads.lt](../conformance/cycles/threads.lt), [cycles/two_handles.lt](../conformance/cycles/two_handles.lt).
