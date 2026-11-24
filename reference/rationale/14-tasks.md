# Rationale: Tasks, shared state and parallelism

Stilt's concurrency keeps one promise above the others: a program means one thing, whatever runs it. Tasks, shared values and parallel calls each give up some freedom of scheduling to keep it, and the sections below say where.

## Tasks

A program that fetches two pages waits for the first before it asks for the second, unless it can start both. Most languages give such code a colour. In Rust, JavaScript and Python, an async function is awaited only from another async function, and a library is written twice, or ties its users to one executor. Stilt makes concurrency an effect ([tasks.async](../14-tasks.md#tasks.async)), as Zig makes it an `Io` chosen in `main`. A function that starts tasks says so in its row, and its callers pass the effect on as any other. The handler that `main` installs decides whether tasks run on threads or one after the other ([tasks.std-task](../14-tasks.md#tasks.std-task)). One library then serves every scheduler.

A task's function captures by copy ([tasks.values-in-tasks](../14-tasks.md#tasks.values-in-tasks)), as every closure does. So tasks share no place, and need no rule of their own against data races. A task's function raises nothing ([tasks.task-functions](../14-tasks.md#tasks.task-functions)). Otherwise `Task<T>` would need the error type, which a `Result` already carries, and a scope gives structured failure where you want it. It performs no user-defined effect, because that effect's handler belongs to the code that started the task. That code may have left the `with` by the time the task performs the effect.

A `with` of an `async` handler waits for its tasks ([tasks.with-waits](../14-tasks.md#tasks.with-waits)). No task outlives the block that started it, so a dropped handle never leaks a running computation.

## The sequential run

A program's meaning is its run under `task.sequential()` ([tasks.sequential-run](../14-tasks.md#tasks.sequential-run)), and every handler gives that run's output ([tasks.same-output-under-every-handler](../14-tasks.md#tasks.same-output-under-every-handler)). Output in the order that threads produce it, as in Go or Java, would make a program's meaning depend on the scheduler. No test could pin it, and a failure under threads couldn't be reproduced. Forbidding tasks to print, so that every write stays in the code that starts them, would also keep one meaning. Keeping a task's output in the sequential order does the same and leaves `print` usable everywhere. The sequential handler is then a debugger. A program that misbehaves under threads, in the order of its files or its network, runs the same under `task.sequential()`, as the reference interpreter runs it.

The cost is that output from a task is held until the tasks before it end. The order in which tasks reach files, the network and the clock isn't part of the meaning ([tasks.unordered-io](../14-tasks.md#tasks.unordered-io)), because fixing it would serialize every task that touches the world.

The Reference fixes the output, and leaves to each implementation how it keeps the order. The compiler's `task.threads()` runs each task on a thread of a pool. It makes the storage of each captured value unique at `spawn`, so that no reference count is shared between threads. It keeps a task's output as a tree of segments, one for each task, inserted at its `spawn` and written out in order as each task ends. Some tasks run where `spawn` starts them, as under `task.sequential()`, with the same output:

- a task started inside a `when`'s block, so that a `when` of it on a held value panics where the sequential run's does;
- a task started when 512 tasks already run, or when no thread can be started;
- a task of a scope started anywhere but directly in the scope's closure, outside every `catch`.

Fibers on an event loop would be a third handler with the same meaning, but they need the runtime to switch stacks on every target.

## Scopes

A task that can fail gives a `Result`, and a scope ([tasks.scopes](../14-tasks.md#tasks.scopes)) turns that into structured failure. Its tasks may raise, and the first raise in the sequential order is the scope's ([tasks.scope-failure](../14-tasks.md#tasks.scope-failure)). The first raise in time would make the result depend on the scheduler, while the first in the sequential order keeps the result the sequential run's. Cancelling the tasks after it, and dropping what they would print, keeps the output the sequential run's too. What they do to files or the network before they are cancelled can't be undone, which is why the order of those uses isn't part of the meaning.

A scope never outlives its function ([tasks.scope-that-escapes](../14-tasks.md#tasks.scope-that-escapes)), by the check that keeps a non-escaping parameter in its call. So no task is started in a scope that has ended.

Under threads, a cancelled task, or a scope's function past the raise that cuts it, runs on unseen until it ends. Nothing waits for it. It stops for good at a panic, an `exit`, a read of stdin or a `when`, and keeps what its frames hold until the program ends. A debug build then skips its check at exit that every count is back to zero, because that check can't tell what such a thread holds from a leak.

## Shared values

Tasks share no place, so a value that many tasks update needs one identity, which `Shared<T>` gives ([shared.std-sync](../14-tasks.md#shared.std-sync)). Stilt takes Verona's behaviour-oriented concurrency for it. A `Shared<T>` is reached only inside `when` ([shared.when](../14-tasks.md#shared.when)), which holds every value it names at once. So no program takes two locks in an order that another reverses.

Three alternatives are left out:

- **Locks and mutexes**, as in Rust, Go and Java. They deadlock when two are taken in opposite orders, which `when` rules out by holding all its values at once.
- **An asynchronous `when`**, as in Verona. It queues its block and returns at once. Stilt's `when` waits, so code reads in the order it runs, and a block's result is the `when`'s value.
- **`Send` and `Sync` traits**, as in Rust. They would say which values may cross to a task, which the modes already say, inferred, with nothing written ([shared.tasks-and-modes](../14-tasks.md#shared.tasks-and-modes)).

The blocks of one value run in the sequential order ([shared.when-order](../14-tasks.md#shared.when-order)). In the order that threads reach them, the output would depend on the scheduler. Some parallelism is given up: tasks that reach one value wait for the order the sequential run gives them. A program that shares nothing runs as freely as tasks let it.

In the compiler, a `Shared<T>` is a cown: a handle on its value. `Shared.new` marks it shared with everything the value reaches, so that their counts change by atomic instructions. A `when` holds all its values at once, from a table of the values held and of the thread that holds each, so that no order of locks is needed. Under threads, a `when` waits before it holds its values. It waits until no task that the sequential order runs before its point, and that hasn't ended, may still reach a handle or raise. Then the blocks of one value run in the sequential order, and none runs in code that a raise before it cancels.

## Holding shared values

A `when` inside another could wait for a value while it holds one. Whether that deadlocks would depend on the order in which other tasks take their values, which no check sees. So the fact `locks` marks code that runs a `when`, and a `when` whose block has it is an error ([shared.locks](../14-tasks.md#shared.locks)). The fix is one `when` that names both values, which holds them at once. A call through a function value isn't a site of `locks`. Almost no closure called in a block runs a `when`, and every such call would otherwise be an error.

What the check can't see is caught where it happens. A `when` reached through a function value or a handler's body, on a value already held, panics with `deadlock` ([shared.when-on-value-already-held](../14-tasks.md#shared.when-on-value-already-held)), because under threads it would wait for itself. A reentrant lock, as Java's `synchronized` is, would hold the value again. Then the inner block could write a place that the outer block has lent `inout`, and the blocks of one value would stop running in the sequential order. The kind doesn't count against `without panic`, as `overflow` doesn't, because every block that calls a function value could reach it. `without locks` is the promise that rules it out.

Two names of one `when` may reach one value, as `transfer(acc, acc, n)` does. The call is reasonable, so it doesn't panic. Instead, the law of exclusivity counts the names as one binding ([shared.names-that-may-be-one-place](../14-tasks.md#shared.names-that-may-be-one-place)). That keeps copying `inout` arguments in and out, as the reference interpreter does, equal to writing them in place, as the compiler does. Writing `inout` arguments back in a fixed order would copy every `inout` argument rooted in a `when`'s name, a hidden cost. The result would still depend on the order of the parameters. The cost of the rule is that `swap(inout a.balance, inout b.balance)` is written with a local, as for one binding. The Lean model shows that the accesses this rule accepts are disjoint even when the names reach one value, and that no two running `when`s hold one value (`formal/Stilt/Interactions/Held.lean`).

## Continuations

A continuation resumed by another task would run the code after a performance on another thread than the code before it. It would run with the stack, the places and the held values of the first thread. Nothing would say what that means. Any construct that moved a continuation between threads would have to define it for `inout` accesses, held values and the order of output. Three rules written for other reasons already prevent it. The Reference states their consequence in a paragraph of its own ([tasks.continuations-stay-in-task](../14-tasks.md#tasks.continuations-stay-in-task)), so that a change to any of the three can't lose it unnoticed.

In return, handlers need no thread safety. A handler's captures, its bodies' stacks and the frames of its continuation stay on one thread, so the compiler's stacks of bodies need no lock. The Lean model shows that a task whose function's row holds no user-defined effect hands no operation to code outside it (`formal/Stilt/Interactions/Tasks.lean`).

Continuations that move between threads, as a work-stealing scheduler of fibers moves them, would need the runtime to switch stacks on every target. Every value that a continuation's frames hold would also have to be `portable`.

## Parallel calls

Much parallel code is simpler than tasks: map a list, run two computations, fill a list in place. `std.par` ([par.std-par](../14-tasks.md#par.std-par)) does it with closures that perform nothing ([par.what-runs-in-parallel](../14-tasks.md#par.what-runs-in-parallel)). So the parallel result is the sequential one ([par.sequential-meaning](../14-tasks.md#par.sequential-meaning)), and no program can tell how many threads ran it. `par.map(xs, f)` reads as `xs.map(f)`, and may run on every core.

The functions live in a module of their own, outside the prelude and outside the methods of `List`, so that no program's own names change meaning. Their closures can't raise. Which raise reached the caller would depend on which call ran first, unless every call waited for the ones before it. A panic is reported as the sequential run's first ([par.panics](../14-tasks.md#par.panics)) for the same reason.

A fold from left to right can't run in parallel. A fold over a tree that the scheduler chooses would give a float sum that changes with the thread count. So `fold` combines in a tree that the list's length alone fixes ([par.fold-tree](../14-tasks.md#par.fold-tree)). A float fold has the same bits on every machine, though it may differ from a loop. There is no `sum` for each number type: `fold` with `+` says the same, and the core library has no trait for addition.

Every binding of a core module is `calm` and `portable`, so `std.par` belongs to core ([par.core-tier](../14-tasks.md#par.core-tier)). E0431 needs a `Shared<T>` or a view, which only the advanced tier has.

The compiler runs `map`, `each` and `fold` in parts on a pool of threads, the calling thread among them. It runs `both` on two threads, with `f` on the calling thread. A fold's parts are subtrees of its tree, which the calling thread combines as the tree says. A part that panics stops its thread, and the calling thread reports the first panic in order once every part before it has ended. A call over a few elements runs on the calling thread.

## Facts of tasks, shared values and parallel calls

`spawn` keeps its function, so a call of it is a call through a stored function value, which may not end ([tasks.implicit-effects-and-capabilities](../14-tasks.md#tasks.implicit-effects-and-capabilities)). It has the capability `spawn`, reached through `async` and not through `io`. So a function can start tasks that only compute without reaching the world. A parallel call has no capability ([par.implicit-effects-and-capabilities](../14-tasks.md#par.implicit-effects-and-capabilities)), because it starts no task that a program can observe.

Reference counts become atomic only where another thread may reach an object, and atomic updates cost time. `stilt show` prints each operation that may make them so ([par.atomic-sites](../14-tasks.md#par.atomic-sites)), so that the cost of sharing has a visible cause. Once a call starts, each closure that another thread calls is marked shared with what it captures. So is what the list's elements reach through an object that something else references too. A call of `spawn` marks the task handles that its function reaches, because the code that started those tasks may wait for them too. The fact is printed at the line, not after the signature, because it says how a function keeps its counts, and nothing that its callers rely on.

## Cycles

Values are freed by reference counting, and a value can't reach itself through values alone. A write changes the place it names, and a value that two places hold is copied before either changes. A `Shared<T>` is the one exception ([cycles.through-shared-values](../14-tasks.md#cycles.through-shared-values)): every copy of a handle reaches one value, and a count alone never frees a cycle. Graphs, lists that know their neighbours, and observers that know their subject all make such cycles.

Stilt frees them ([cycles.freeing](../14-tasks.md#cycles.freeing)), and freeing runs no code ([cycles.freeing-is-unseen](../14-tasks.md#cycles.freeing-is-unseen)). A task's handle that goes stops nothing, because its task runs as the sequential run runs it. So freeing changes nothing a program does, and a debug build's check at exit holds of every program ([cycles.check-at-exit](../14-tasks.md#cycles.check-at-exit)). A release build skips the check, because its process gives back its memory as it ends.

Four alternatives are left out:

- **Rejecting types that can form a cycle.** That forbids the programs `Shared<T>` exists to write, and a closure that captures a handle is enough to make one.
- **Leaking cycles**, as Rust and Swift do. "No leaks" would then be false of every program that links handles. A server that links them would grow until it ran out of memory.
- **Weak handles**, as Rust's `Weak` and Swift's `weak`. They aren't needed once cycles are collected. A weak handle's value can go while a program holds it, so reading one asks about freeing, which no Stilt program can ask.
- **A tracing collector for the whole heap**, as in Go and Java. It would pause programs that make no cycle, and lose the counts that let a write change a value in place when nothing else references it.

`stilt show` writes which types can form a cycle ([cycles.can-form-cycle](../14-tasks.md#cycles.can-form-cycle)), so you see where collection may be needed. The test is broad on purpose. A function or handler type can reach any handle, because a closure may capture one. A type parameter or a pack may be any type, and a `Lazy<T>` has a function that may capture a handle. The fact limits nothing, because every such type is legitimate.

The compiler's runtime collects cycles by trial deletion, Bacon and Rajan's synchronous algorithm ("Concurrent Cycle Collection in Reference Counted Systems", ECOOP 2001, section 3), as Nim's ORC does. Everything a handle reaches is marked shared, so only shared objects can be in a cycle, and only they are looked at. The collector works in three parts:

- **Candidates.** A release of a shared object that others still reference makes it a candidate, because the release that lets a cycle go leaves its counts above zero. An object freed meanwhile stops being a candidate. No object is a candidate until a shared value first holds a handle or a task's handle. So a program that never links handles pays one load of a flag on each release of a shared object.
- **Collections.** A collection lowers each count by the references that the shared objects the candidates reach hold to one another. What is still above zero is referenced from outside, so it and all it reaches get their counts back. What stays at zero is a cycle, or what only cycles reach, and is freed. A collection runs at these points:
  - when `Shared.new` makes a handle or a `when` lets one go, if there are 1,024 candidates and twice as many as lived through the last collection;
  - at the same points, if the heap holds twice what it held after the last collection, and at least 64 MiB more;
  - when an allocation finds the heap full;
  - when the program ends, before the check at exit.
- **Safety.** A collection runs only while no other thread runs the program's code. It doesn't look into the value of a handle that a `when` holds, whose block may be writing its place.

Once a program links handles, the first release of each shared object that others still reference takes a lock, and a collection pauses for what the candidates reach. A collector on another thread, running while the program runs, would remove the pause. But it needs every release to be recorded, which costs the programs that share values across threads.
