# 15. Inferred facts and limits

Besides its signature, each function has facts that the compiler infers from its body. They say whether the function can panic or overflow, whether it allocates, whether it may not end, and whether it copies data that another value shares. They also say whether it holds shared values, which capabilities below `io` it reaches, and whether its own code holds `unsafe` blocks or names C functions. A `without` clause turns each of them but `foreign` into a promise that `check` keeps, and verification proves from each body alone that some checks can't fail. [Effects and handlers](12-effects.md) defines panics and overflow, [Modes and exclusivity](13-modes.md) shared writes, [Tasks, shared state and parallelism](14-tasks.md) `locks`, and [Builds](20-builds.md) `unsafe` and `foreign`.

## Inferred facts

<a id="facts.inferred-facts"></a>
Each function and method has **facts** that the compiler infers from its body and from the facts of what the body names. These are the facts that a limit names, or that a function's own code has:

| Fact | The function | Its sites |
| --- | --- | --- |
| `panic` | can panic, with a kind that counts against `without panic` | [effects.panicking-operations](12-effects.md#effects.panicking-operations), [facts.map-element-places](#facts.map-element-places) |
| `overflow` | can overflow an integer | [effects.overflow-effect](12-effects.md#effects.overflow-effect) |
| `alloc` | can allocate | [facts.allocation](#facts.allocation), [facts.native-allocation](#facts.native-allocation) |
| `div` | may not end | [facts.div](#facts.div) |
| `copy` | can copy data that another value shares | [facts.copy](#facts.copy) |
| `locks` | holds shared values | [shared.locks](14-tasks.md#shared.locks) |
| `fs`, `net`, `clock`, `env`, `console`, `rand`, `spawn`, `exec` | reaches files, the network, the clock, the environment, the console or randomness, starts tasks, or runs other programs | [facts.capabilities](#facts.capabilities) |
| `unsafe` | holds an `unsafe` block in its own code | [c.unsafe-and-foreign](20-builds.md#c.unsafe-and-foreign) |
| `foreign` | names foreign functions in its own code | [c.unsafe-and-foreign](20-builds.md#c.unsafe-and-foreign) |

Every fact but `unsafe` and `foreign` is inherited: a function has it when its body names a function that has it ([facts.inference](#facts.inference)). `unsafe` and `foreign` are facts of a function's own code alone. Every fact but `foreign` is a limit of a `without` clause ([facts.without](#facts.without)). Each of those limits but `unsafe` is a **limitable fact**, part of a package's API ([versions.limitable-facts](21-versions.md#versions.limitable-facts)).

A function also has facts that no limit names:

- the parameters it consumes ([values.consumed-parameters](05-values.md#values.consumed-parameters));
- the modes of its bindings ([modes.bindings-and-axes](13-modes.md#modes.bindings-and-axes));
- its in-place parameters ([facts.in-place-parameters](#facts.in-place-parameters));
- the checks that verification proves ([facts.shown-proofs](#facts.shown-proofs));
- the operations that may make reference counts atomic ([par.atomic-sites](14-tasks.md#par.atomic-sites)).

A module has its tier as a fact ([program.module-tier](04-programs.md#program.module-tier)), and a type has whether it can form a cycle ([cycles.can-form-cycle](14-tasks.md#cycles.can-form-cycle)).

Tests: [effects/implicit_effects.lt](../conformance/effects/implicit_effects.lt), [implicit/callees](../conformance/implicit/callees/), [implicit/panicking_function_values.lt](../conformance/implicit/panicking_function_values.lt), [implicit/unlimited_alloc.lt](../conformance/implicit/unlimited_alloc.lt).

<a id="facts.implicit-effects"></a>
`panic`, `overflow`, `alloc`, `div` and `copy` are the **implicit effects**: effects that the compiler infers from bodies, and that no signature writes. Writing `panic` or `alloc` as an element of a row is E0501, *effect name as a row variable* ([effects.effect-names](12-effects.md#effects.effect-names)). In a row, `overflow`, `div` and `copy` are names of row variables, as any lowercase name is ([facts.spelling](#facts.spelling)). So a body's implicit effects are never part of a function's type.

Tests: [effects/implicit_effects.lt](../conformance/effects/implicit_effects.lt), [effects/row_elements.lt](../conformance/effects/row_elements.lt), [implicit/rows.lt](../conformance/implicit/rows.lt), [names/row_elements.lt](../conformance/names/row_elements.lt).

<a id="facts.inference"></a>
A function's implicit effects are the union of:

- the **sites** in its own body: the operations that have an effect themselves;
- the implicit effects of every function it names, whether it calls the function or uses it as a value, a foreign function's being those that [c.effects](20-builds.md#c.effects) gives it;
- the implicit effects of the body of every closure literal and handler literal it contains ([handlers.implicit-effects-and-capabilities](12-effects.md#handlers.implicit-effects-and-capabilities)).

A call of a trait method whose impl is known where the call is written names that impl's method. So do the calls behind operators such as `==` and `<`, and behind interpolation ([traits.operators](11-traits.md#traits.operators)). Instantiating a generic function with concrete types names the impl methods that its bounds require, so `sort` on a list of records names their `Ord` impl. A call through a bound, inside generic code, is a call through a function value ([facts.calls-through-function-values](#facts.calls-through-function-values)). The functions of a recursive group are solved together, as a fixed point over the graph of what each body names. `locks` and the capabilities are inferred the same way, from their own sites.

Tests: [effects/without_panic_inherits](../conformance/effects/without_panic_inherits/), [effects/without_panic_map_store](../conformance/effects/without_panic_map_store/), [effects/without_panic_traits](../conformance/effects/without_panic_traits/), [implicit/body_error_no_effects](../conformance/implicit/body_error_no_effects/), [implicit/callees](../conformance/implicit/callees/), [implicit/closures](../conformance/implicit/closures/), [implicit/deep_bounds.lt](../conformance/implicit/deep_bounds.lt), [implicit/recursion](../conformance/implicit/recursion/), [implicit/traits](../conformance/implicit/traits/), [implicit/without_panic_accepted](../conformance/implicit/without_panic_accepted/), [packages/ungranted_trait](../conformance/packages/ungranted_trait/), [foreign/c_facts.lt](../conformance/foreign/c_facts.lt).

<a id="facts.calls-through-function-values"></a>
A call through a function value adds no implicit effect, no `locks` and no capability. They are counted where the closure literal is written, or where the named function is referenced ([facts.inference](#facts.inference)). So every panic, every allocation and every capability belongs to the module whose source text holds the operation or names the native. Code limited by a `without` may call a function value that it receives, wherever the value was made. `without fs` promises that the code's own source reaches no file, and `List.fold` keeps its caller's limits whatever callback it is given.

`div` is the one exception: a call through a stored function value is a site of `div` ([facts.div](#facts.div)). Performing an operation of an effect counts as a call through a stored function value ([handlers.implicit-effects-and-capabilities](12-effects.md#handlers.implicit-effects-and-capabilities)).

Tests: [capabilities/accepted.lt](../conformance/capabilities/accepted.lt), [capabilities/closure](../conformance/capabilities/closure/), [declarations/function_limits.lt](../conformance/declarations/function_limits.lt), [effects/implicit_effects.lt](../conformance/effects/implicit_effects.lt), [effects/without_panic_inherits](../conformance/effects/without_panic_inherits/), [implicit/closures](../conformance/implicit/closures/), [implicit/traits](../conformance/implicit/traits/), [implicit/without_alloc](../conformance/implicit/without_alloc/), [implicit/without_panic_accepted](../conformance/implicit/without_panic_accepted/).

<a id="facts.bodies-with-errors"></a>
A body with an error has no implicit effects. So it causes no E0204, *fact beyond a `without` limit*, in the bodies that name it. When it runs, it panics with `check-error` where the error is reached ([program.programs-with-errors](04-programs.md#program.programs-with-errors)).

Tests: [implicit/body_error_no_effects](../conformance/implicit/body_error_no_effects/).

<a id="facts.interfaces"></a>
A function's facts are recorded per function in its module's interface, in an artifact kept apart from the signatures. The checks of the limits, lints and tools read them, and type checking never does. An edit of a body can change that function's facts. It then invalidates only the checks and lints that read them, never the type checking of its callers.

Tests: [implicit/callees](../conformance/implicit/callees/), [implicit/panicking_function_values.lt](../conformance/implicit/panicking_function_values.lt).

## Showing facts

<a id="facts.visibility"></a>
`stilt show` and the language server print a function's facts in a bracket after its signature, as in `fn totals(orders: List<Order>) -> List<(str, f64)> [panic, alloc]`. Each fact comes with the line of the body that causes it. The bracket holds:

- its implicit effects, `overflow` after `panic`, and `locks`;
- its in-place parameters, as `in place xs`, each with the line that makes it in place ([facts.in-place-parameters](#facts.in-place-parameters));
- the checks that verification proves ([facts.shown-proofs](#facts.shown-proofs));
- its capabilities, after all of these, as `io: fs, clock`, in the order of [facts.capabilities](#facts.capabilities), or nothing more for a function with none;
- `unsafe` and `foreign: crc32`, last ([c.unsafe-and-foreign](20-builds.md#c.unsafe-and-foreign)).

A module's skeleton, its signatures and doc summaries, leaves every fact out.

Checked by: the toolchain's tests of `stilt show` and of the language server (`compiler/stilt-cli/tests/show.rs`, `compiler/stilt-cli/tests/lsp.rs`), and the facts suite, which `just facts` checks (`compiler/stilt-cli/tests/facts.rs`).

<a id="facts.facts-suite"></a>
The facts suite (`tests/facts/`) has one annotation for each fact that `stilt show` prints at a line, beside the annotations of the other chapters. This chapter's annotations are:

- `PANIC`, `OVERFLOW`, `ALLOC`, `DIV`, `COPY` and `LOCKS`;
- `IN-PLACE xs`;
- `FS`, `NET`, `CLOCK`, `ENV`, `CONSOLE`, `RAND`, `SPAWN` and `EXEC`, one for each capability;
- `PROVED bounds`, `PROVED divide-by-zero` and `PROVED missing-key`.

Its expected facts are derived from the rules of this chapter by reasoning, never from an implementation.

Checked by: `just facts` (`compiler/stilt-cli/tests/facts.rs`).

## Limits

<a id="facts.without"></a>
A `without` clause names **limits**. It stands in a module's header ([program.module-header](04-programs.md#program.module-header)) or after a function's signature ([declarations.limits](10-declarations.md#declarations.limits)). The limits are `panic`, `overflow`, `alloc`, `div`, `copy`, `locks`, the eight capabilities and `unsafe` (the `limits` production, [syntax.programs](03-syntax.md#syntax.programs)).

Code limited by `without L` holds no site of the fact `L`, in any module. This covers its own sites and the sites that it inherits from the functions it names. A module's limit covers the bodies of its functions, and a function's limit covers its own body. Each operation that breaks a limit is E0204, *fact beyond a `without` limit*. Such an operation is a site itself, or names a function that has the fact. Operations on one line beyond one limit are one E0204, at the first of them, which names the others.

A function limited by `without L`, through its module or its own clause, counts as one without `L` wherever it is named, directly or through other functions. So its own sites are errors where they are written, and its callers get none. Test bodies, doc examples and properties are exempt from every limit. `unsafe` limits a function's own code alone ([c.without-unsafe](20-builds.md#c.without-unsafe)).

Tests: [capabilities/accepted.lt](../conformance/capabilities/accepted.lt), [capabilities/limits.lt](../conformance/capabilities/limits.lt), [capabilities/module_limit.lt](../conformance/capabilities/module_limit.lt), [declarations/function_limits.lt](../conformance/declarations/function_limits.lt).

<a id="facts.spelling"></a>
The limits other than `unsafe` are contextual keywords, read as limits only after `without` ([lexical.contextual-keywords](02-lexical.md#lexical.contextual-keywords)). `unsafe` is a reserved word. Elsewhere, the contextual keywords are names: of locals, functions and parameters, and, in a row, of row variables, as any lowercase name is. The exceptions are `panic` and `alloc`, which a row can't name (E0501, *effect name as a row variable*, [effects.effect-names](12-effects.md#effects.effect-names)). A limit named twice is E0202, *`without` given twice*, at its second occurrence. A word after `without` that isn't a limit, as `total`, is E0100, *syntax error*.

Tests: [capabilities/repeated.lt](../conformance/capabilities/repeated.lt), [capabilities/spelling.lt](../conformance/capabilities/spelling.lt), [promises/repeated.lt](../conformance/promises/repeated.lt), [promises/spelling.lt](../conformance/promises/spelling.lt), [promises/total_module.lt](../conformance/promises/total_module.lt), [promises/unknown_limit.lt](../conformance/promises/unknown_limit.lt).

## Panics, overflow and allocation

<a id="facts.map-element-places"></a>
The sites of `panic` and `overflow` are those of [effects.panicking-operations](12-effects.md#effects.panicking-operations) and [effects.overflow-effect](12-effects.md#effects.overflow-effect). Their limits are those of [effects.without-panic](12-effects.md#effects.without-panic) and [effects.without-overflow](12-effects.md#effects.without-overflow). An assignment whose place goes through a map element, as `m[k].f = v`, reads `m[k]` as an expression would, then stores the changed value back ([std.map-element-places](17-std.md#std.map-element-places)). So it adds `panic`, as a read of `m[k]` does, and `alloc`, as every place through an index does ([facts.allocation](#facts.allocation)).

Tests: [effects/without_panic_map_element_place.lt](../conformance/effects/without_panic_map_element_place.lt).

<a id="facts.allocation"></a>
These operations add the implicit effect `alloc`:

- a list literal, a closure literal, a key path, which is a closure ([expressions.key-paths](08-expressions.md#expressions.key-paths)), and a string literal that interpolates;
- a record literal of a recursive type, and the constructor of a variant with a payload of a recursive type, called or named as a function value;
- an assignment, a compound assignment and an `inout` argument whose place goes through an index, as in `xs[i] = v`, `m[k] += 1` and `f(inout xs[0])`, unless the write is in place ([facts.writes-in-place](#facts.writes-in-place));
- a `yield` of such a place ([projections.yield](13-modes.md#projections.yield));
- a `with`, which installs its handler, and a performance of an operation of an effect, whose rest a handler may keep ([handlers.implicit-effects-and-capabilities](12-effects.md#handlers.implicit-effects-and-capabilities));
- a `for` over an `Iter`, which keeps the loop's state as it pulls ([views.for-over-view](13-modes.md#views.for-over-view)).

A type is **recursive** when its declaration names it again, directly or through the declarations of the types it names ([declarations.recursive-types](10-declarations.md#declarations.recursive-types)). The types it names include its type arguments, and the parameter, result and error types of its function types. Naming a constant adds nothing, and neither does making, copying, reading or writing an array ([generics.array-effects](07-types.md#generics.array-effects)).

Tests: [declarations/function_limits.lt](../conformance/declarations/function_limits.lt), [implicit/allocating_natives.lt](../conformance/implicit/allocating_natives.lt), [implicit/without_alloc](../conformance/implicit/without_alloc/), [names/repeated_without_is_ignored.lt](../conformance/names/repeated_without_is_ignored.lt).

<a id="facts.native-allocation"></a>
A native function ([declarations.native-items](10-declarations.md#declarations.native-items)) allocates, but for those this list names, which don't:

- the native methods of the integer and float types;
- of `str`: `len`, `is_empty`, `contains`, `starts_with`, `ends_with`, `find`, `rfind`, `count`, `char_count`, the `is_ascii` tests, and the parsers `to_i8` to `to_f64`;
- of `List<T>`: `len`, `is_empty`, `get` and `with_ptr`; of `Map<K, V>`: `len`, `is_empty`, `contains` and `get`;
- the natives of `std.array`, which hold an array inline ([generics.array-effects](07-types.md#generics.array-effects));
- of `std.view`: `View.of`, `View.all`, `len`, `is_empty` and `view` of `View<T>`, `view.get` and `view.part`, since a view is held inline ([views.what-view-is](13-modes.md#views.what-view-is));
- the functions of `std.math`;
- the natives of `std.meta`, whose accessors read a shape and whose `make`s allocate where the type they make does ([meta.accessor-effects](16-meta.md#meta.accessor-effects));
- of `std.c`: `null`, the `is_null`, `offset`, `address`, `read` and `write` of `Ptr<T>`, and `Str.is_null`;
- `unix_ms`, `monotonic_ns` and `sleep_ms` of `std.clock`, and `entropy` of `std.random`;
- a native whose result type is `Never`, as `panic`, `unreachable` and `exit` are, which ends the program.

Every other native allocates, so a native the library adds allocates until this list names it. A method of an impl that no source declares, as a primitive type's impl or a structural one ([traits.structural-impls](11-traits.md#traits.structural-impls)), allocates when its declared result type names `str`, `List` or `Map`. So `str.split`, `List.push`, `Shared.new`, `Lazy.new`, every function of an iterator, `print` and the built-in `show` allocate, while `str.len`, `List.get` and `eq` don't.

Tests: [effects/natives_under_limits.lt](../conformance/effects/natives_under_limits.lt), [implicit/allocating_natives.lt](../conformance/implicit/allocating_natives.lt), [implicit/allocation_free_natives.lt](../conformance/implicit/allocation_free_natives.lt), [implicit/without_alloc](../conformance/implicit/without_alloc/).

<a id="facts.without-alloc"></a>
Code limited by `without alloc` holds no operation that adds `alloc`, its own or one that it inherits, checked as every limit is ([facts.without](#facts.without)). Under the limit, a function holds the storage of its list parameters ([facts.own-storage](#facts.own-storage)). Its writes through an index can then be in place, and its callers make the copy that a shared argument needs ([facts.copy-at-call](#facts.copy-at-call)). A list operation counts as allocating even when the list isn't shared and has room.

Tests: [declarations/function_limits.lt](../conformance/declarations/function_limits.lt), [effects/natives_under_limits.lt](../conformance/effects/natives_under_limits.lt), [implicit/allocating_natives.lt](../conformance/implicit/allocating_natives.lt), [implicit/allocation_free_natives.lt](../conformance/implicit/allocation_free_natives.lt), [implicit/unlimited_alloc.lt](../conformance/implicit/unlimited_alloc.lt), [implicit/without_alloc](../conformance/implicit/without_alloc/).

Checked by: the compiler's debug builds, in which a function limited by `without alloc` counts its frames, one that allocates runs with the count at 0, and an allocation while the count isn't 0 ends the program with a report of the bug; `just run`, `just examples` and `just differential` run them over the conformance suite, the guide's examples, the showcases and generated programs, and find none.

## Updates in place

<a id="facts.own-storage"></a>
At a point of a body, a binding whose type is a copy-on-write type ([modes.copy-on-write-types](13-modes.md#modes.copy-on-write-types)) **holds its own storage** when each of its assignments before the point gives it storage of its own. An assignment of the whole binding does when it is one of these:

- the declaration of a parameter, `let` or `inout`, of a function limited by `without alloc`, through its own clause or its module's header;
- an assignment that gives the binding a list literal;
- an assignment that names whole, at its last use ([facts.last-use](#facts.last-use)), a binding that holds its own storage there.

A binding's declaration counts as an assignment, a parameter's where the body starts, and a `let` binding's one assignment is its declaration. A declaration whose pattern takes the value apart gives no storage of its own, and a binding that a pattern of a `match`, an `if let`, a `for`, a `catch` or a closure literal's parameters binds holds none. A binding's **assignments before a point** are the last one before the point, in source order, that is a statement of a block holding the point, and each one after that one and before the point. When the point is inside a loop that this last one is outside of, they are also each one inside the loop: its body, and a `while`'s condition. So after `var ys = c` and `if d { ys = xs }`, both assignments are before a write that follows, and an assignment after a write in a loop's body is before it, for the next turn.

Tests: [promises/in_place.lt](../conformance/promises/in_place.lt), [promises/in_place_elements.lt](../conformance/promises/in_place_elements.lt), [promises/in_place_rejected.lt](../conformance/promises/in_place_rejected.lt).

<a id="facts.last-use"></a>
A use of a binding is its **last use** when no use of the binding follows it in source order. A use inside a loop that the binding's declaration is outside of is never a last use. A use inside a closure literal counts as a use at the literal.

Tests: [promises/in_place.lt](../conformance/promises/in_place.lt), [promises/in_place_elements.lt](../conformance/promises/in_place_elements.lt), [promises/in_place_rejected.lt](../conformance/promises/in_place_rejected.lt).

<a id="facts.writes-in-place"></a>
An assignment or compound assignment whose place is `b[i]` is **in place**, and adds no `alloc`, when both of these hold:

- `b` names a binding of type `List<T>` that holds its own storage there;
- the modification isn't shared ([modes.shared-writes](13-modes.md#modes.shared-writes)).

When `T` isn't a copy-on-write type and holds no type parameter, an assignment or compound assignment whose place goes on from such a `b[i]` is in place too. Its place goes on through fields, tuple elements and elements of arrays, as `b[i].x`, `b[i].at.0` and `b[i].cells[j]` do. Such a `T` is a number type, `bool`, `()`, or a record, tuple, variant type or array made only of them. A call of `view.into` or `view.split` whose `inout` argument names whole such a binding is in place too ([projections.writable-views](13-modes.md#projections.writable-views)).

Every other place through an index allocates:

- a store into a map;
- `b[i][j]`, `b[i].f` and `b[i].0` when `T` is a copy-on-write type or holds a type parameter;
- an `inout` argument `b[i]`;
- a `yield` of `b[i]`.

Tests: [checking/error_typed_arguments.lt](../conformance/checking/error_typed_arguments.lt), [implicit/without_alloc](../conformance/implicit/without_alloc/), [promises/in_place.lt](../conformance/promises/in_place.lt), [promises/in_place_elements.lt](../conformance/promises/in_place_elements.lt), [promises/in_place_elements_rejected.lt](../conformance/promises/in_place_elements_rejected.lt), [promises/in_place_rejected.lt](../conformance/promises/in_place_rejected.lt), [promises/in_place_views.lt](../conformance/promises/in_place_views.lt).

<a id="facts.in-place-parameters"></a>
A parameter of a function limited by `without alloc` is **in place** when its storage reaches a write in place. It does when the body does one of these:

- writes the parameter in place;
- writes in place a `var` binding that took its storage ([facts.own-storage](#facts.own-storage));
- passes the parameter, or such a binding, named whole, to an in-place parameter of a callee without allocating there ([facts.copy-at-call](#facts.copy-at-call)).

A callee counts when the call names it: a function, a method, or a trait method whose impl is known ([facts.inference](#facts.inference)). A `let` parameter passed on this way must be passed at its last use. Recursive groups are solved as a fixed point over the call graph, starting from no parameter in place. A parameter of a function that isn't limited by `without alloc`, or of a native function, is never in place.

Tests: [promises/in_place.lt](../conformance/promises/in_place.lt), [promises/in_place_elements.lt](../conformance/promises/in_place_elements.lt), [promises/in_place_rejected.lt](../conformance/promises/in_place_rejected.lt).

<a id="facts.copy-at-call"></a>
A call that passes an argument to an in-place parameter adds `alloc` at the argument, unless:

- the argument is a list literal, a value that nothing else holds;
- for a `let` parameter, the argument names whole, at its last use, a binding that holds its own storage;
- for an `inout` parameter, the argument names whole a binding that holds its own storage, and the modification isn't shared ([modes.shared-writes](13-modes.md#modes.shared-writes)).

An `inout` argument whose place goes through an index already allocates ([facts.allocation](#facts.allocation)), and this rule adds nothing more to it. The `alloc` stands for the copy that a shared argument needs: the call makes the argument's storage unique, and the callee's writes copy nothing. A function that isn't limited by `without alloc` holds no parameter's storage. Its writes to a parameter through an index allocate, and its calls that pass a parameter on count as allocating. Its callers may pass it a value that is shared.

Tests: [checking/error_typed_arguments.lt](../conformance/checking/error_typed_arguments.lt), [promises/in_place.lt](../conformance/promises/in_place.lt), [promises/in_place_elements.lt](../conformance/promises/in_place_elements.lt), [promises/in_place_rejected.lt](../conformance/promises/in_place_rejected.lt).

<a id="facts.in-place-promise"></a>
A function limited by `without alloc` copies nothing in its body and allocates nothing there. Each of its in-place parameters gets storage that no other value shares, and the function updates it in place. Nothing a program prints depends on where the copy happens: every implementation keeps value semantics ([values.value-semantics](05-values.md#values.value-semantics)). The conformance tests check which programs the limit accepts.

Tests: [promises/in_place.lt](../conformance/promises/in_place.lt), [promises/in_place_elements.lt](../conformance/promises/in_place_elements.lt).

Checked by: also the compiler's tests of in-place updates (`compiler/stilt-cli/tests/consumption.rs`), since where the copy happens is what no program can observe.

## Termination

<a id="facts.div"></a>
Possible non-termination, `div`, is an implicit effect, inferred as the others are ([facts.inference](#facts.inference)). Its sites are:

- a `while` loop, at its `while`, unless it is a counting loop ([facts.counting-loops](#facts.counting-loops));
- a `loop`, at its `loop`;
- a call through a function value, at the call, other than the calls below that add nothing. The value may be one that a field, a local binding, a parameter marked `escaping` or a list holds. It may also be one that a call, an element of a tuple or any other expression gives. A call of `task.spawn` or `s.spawn` is one ([tasks.implicit-effects-and-capabilities](14-tasks.md#tasks.implicit-effects-and-capabilities)), and so is a performance of an operation ([handlers.implicit-effects-and-capabilities](12-effects.md#handlers.implicit-effects-and-capabilities));
- a call of a function of the caller's own **recursive group**, and a use of one as a value, at the call or the name. A recursive group is a strongly connected component of the graph of what each body names. The self-calls of a function whose self-calls all descend ([facts.descending-self-calls](#facts.descending-self-calls)) or all shrink ([facts.shrinking-recursion](#facts.shrinking-recursion)) are not sites.

For `div` alone, a call through a stored function value counts ([facts.calls-through-function-values](#facts.calls-through-function-values)). These calls add nothing, and their sites are counted where the argument is written or the impl named:

- a call through a parameter that isn't marked `escaping`;
- a call of a closure literal where it is written, whose body's sites are the caller's;
- a call through a bound in generic code.

A `for` loop adds nothing. Lists, maps, ranges and the iterators of `std.view` are finite, and nothing modifies a loop's source while the loop runs ([modes.change-while-iterating](13-modes.md#modes.change-while-iterating), [views.for-over-view](13-modes.md#views.for-over-view)). No native function has `div` but `Lazy.get` ([polymorphism.lazy-implicit-effects](07-types.md#polymorphism.lazy-implicit-effects)).

Tests: [promises/termination.lt](../conformance/promises/termination.lt), [promises/termination_rejected.lt](../conformance/promises/termination_rejected.lt), [tasks/spawn_without_div.lt](../conformance/tasks/spawn_without_div.lt), [verification/counting_loops.lt](../conformance/verification/counting_loops.lt), [verification/counting_loops_rejected.lt](../conformance/verification/counting_loops_rejected.lt), [verification/recursion.lt](../conformance/verification/recursion.lt), [verification/recursion_rejected.lt](../conformance/verification/recursion_rejected.lt).

<a id="facts.descending-self-calls"></a>
A function's calls of itself **descend** when one of its `let` parameters, `p`, meets one condition at every self-call in its body. The argument at `p`'s position names a binding that holds a **strict part** of `p`. A strict part is reached from `p` by at least one step, through a field, a tuple element or a variant's payload. The steps may be taken by a pattern that matches `p`, or by a place rooted in `p` made of fields and tuple elements. They may also be taken through a binding that holds a strict part. They are never taken through a call, an index or a function value. Any other recursion has `div`: recursion on an integer, unless its self-calls shrink ([facts.shrinking-recursion](#facts.shrinking-recursion)), recursion on a list, and mutual recursion.

Tests: [promises/termination.lt](../conformance/promises/termination.lt), [promises/termination_rejected.lt](../conformance/promises/termination_rejected.lt), [verification/recursion.lt](../conformance/verification/recursion.lt), [verification/recursion_rejected.lt](../conformance/verification/recursion_rejected.lt).

<a id="facts.without-div"></a>
Code limited by `without div` holds no site of `div`, its own or one that it inherits, checked as every limit is ([facts.without](#facts.without)). Each site is E0204, *fact beyond a `without` limit*, and so is each operation that names a function that has `div`. Code limited by `without panic, div` is **total**: it ends without a panic, unless it overflows an integer, overflows the stack or runs out of memory ([program.exit-statuses](04-programs.md#program.exit-statuses)).

Tests: [promises/termination.lt](../conformance/promises/termination.lt), [promises/termination_rejected.lt](../conformance/promises/termination_rejected.lt), [promises/total_module.lt](../conformance/promises/total_module.lt), [tasks/spawn_without_div.lt](../conformance/tasks/spawn_without_div.lt), [verification/counting_loops.lt](../conformance/verification/counting_loops.lt), [verification/counting_loops_held_rejected.lt](../conformance/verification/counting_loops_held_rejected.lt), [verification/counting_loops_rejected.lt](../conformance/verification/counting_loops_rejected.lt), [verification/recursion.lt](../conformance/verification/recursion.lt), [verification/recursion_rejected.lt](../conformance/verification/recursion_rejected.lt).

## Copies

<a id="facts.copy"></a>
A write that copies shared data, `copy`, is an implicit effect, inferred as the others are ([facts.inference](#facts.inference)). Its sites are each modification that is shared ([modes.shared-writes](13-modes.md#modes.shared-writes)), and each argument that a call copies for an in-place parameter ([facts.copy-at-call](#facts.copy-at-call)). An argument that is both is one site.

Tests: [modes/array_copies.lt](../conformance/modes/array_copies.lt), [modes/consumed_copies.lt](../conformance/modes/consumed_copies.lt), [modes/copies_stored_by_calls.lt](../conformance/modes/copies_stored_by_calls.lt), [modes/copies_stored_in_inout_arguments.lt](../conformance/modes/copies_stored_in_inout_arguments.lt), [modes/copy_scopes.lt](../conformance/modes/copy_scopes.lt), [modes/copy_ways.lt](../conformance/modes/copy_ways.lt), [modes/element_copies.lt](../conformance/modes/element_copies.lt), [promises/copies.lt](../conformance/promises/copies.lt), [promises/copies_after_a_name_defined_twice.lt](../conformance/promises/copies_after_a_name_defined_twice.lt), [promises/copies_read_after_the_body.lt](../conformance/promises/copies_read_after_the_body.lt), [promises/copies_read_by_another_holder.lt](../conformance/promises/copies_read_by_another_holder.lt), [promises/stored_copies.lt](../conformance/promises/stored_copies.lt).

<a id="facts.without-copy"></a>
Code limited by `without copy` holds no site of `copy`, its own or one that it inherits, checked as every limit is ([facts.without](#facts.without)). Fresh values stay within the limit: a `push` on a list that no copy shares, a list literal and a string that interpolates.

Tests: [modes/copies_in_closures_and_branches.lt](../conformance/modes/copies_in_closures_and_branches.lt), [modes/copies_of_held_parts.lt](../conformance/modes/copies_of_held_parts.lt), [modes/handles.lt](../conformance/modes/handles.lt), [modes/shared_writes_along_paths.lt](../conformance/modes/shared_writes_along_paths.lt), [modes/shared_writes_along_paths_accepted.lt](../conformance/modes/shared_writes_along_paths_accepted.lt), [modes/shared_writes_in_when.lt](../conformance/modes/shared_writes_in_when.lt), [program/header_options.lt](../conformance/program/header_options.lt), [program/header_separators.lt](../conformance/program/header_separators.lt), [promises/copies.lt](../conformance/promises/copies.lt), [promises/copies_read_after_the_body.lt](../conformance/promises/copies_read_after_the_body.lt), [promises/copies_read_by_another_holder.lt](../conformance/promises/copies_read_by_another_holder.lt), [promises/stored_copies.lt](../conformance/promises/stored_copies.lt).

## Capabilities

<a id="facts.capabilities"></a>
There are eight **capabilities** below `io`, in this order: `fs`, `net`, `clock`, `env`, `console`, `rand`, `spawn` and `exec`. Each is a fact of a function, inferred as the implicit effects are ([facts.inference](#facts.inference)). A function has the capabilities of the natives it names ([facts.capability-natives](#facts.capability-natives)), of every function it names, and of the bodies of the closure literals and handler literals it contains. A call of a trait method names the impl's method, and recursive groups are solved as a fixed point. Each capability is a limit: `without fs` promises that the code reaches no file through its own source ([facts.without](#facts.without), [facts.calls-through-function-values](#facts.calls-through-function-values)). A program that code runs may reach anything, and what it reaches is no fact of the code. Running a program is the capability `exec`, so code that keeps away from files keeps `without fs, exec`.

Tests: [capabilities/limits.lt](../conformance/capabilities/limits.lt).

<a id="facts.capability-natives"></a>
These natives of `std` have a capability, and no other native has one:

| Capability | Natives |
| --- | --- |
| `console` | `print`, `eprint`, and `std.io`'s `read_line`, `poll_line`, `read_all`, `write`, `ewrite` and `flush` |
| `fs` | every native of `std.fs`; its path functions, `join`, `file_name`, `parent` and `extension`, are not natives and have none |
| `clock` | `std.clock`'s `unix_ms`, `monotonic_ns` and `sleep_ms` |
| `env` | `std.cli`'s `args` and `env` |
| `rand` | `std.random`'s `entropy` |
| `spawn` | `std.task`'s `spawn` and `Scope.spawn` ([tasks.implicit-effects-and-capabilities](14-tasks.md#tasks.implicit-effects-and-capabilities)) |
| `net` | every native of `std.net` ([std.net](17-std.md#std.net)) |
| `exec` | every native of `std.process` ([std.process](17-std.md#std.process)) |

`exit` has no capability, and performs `io` with none ([facts.io-and-capabilities](#facts.io-and-capabilities)). A foreign function has no capability either ([c.effects](20-builds.md#c.effects)).

Tests: [capabilities/limits.lt](../conformance/capabilities/limits.lt).

<a id="facts.io-and-capabilities"></a>
Every native that has a capability other than `spawn` declares `io` in its row. So a function that has such a capability performs `io`: its row holds `io`, or the call is E0502, *effect that doesn't fit the row* ([effects.inference](12-effects.md#effects.inference)). A function may perform `io` without any capability, through `exit` or through a call through a function value. `spawn` is reached through `async` instead, which `task.spawn` performs without `io` ([tasks.std-task](14-tasks.md#tasks.std-task)). So a function may start tasks that only compute. No capability is ever written in a row: there, `fs`, `net` and the others are names of row variables ([facts.spelling](#facts.spelling)).

Tests: [capabilities/accepted.lt](../conformance/capabilities/accepted.lt), [capabilities/spelling.lt](../conformance/capabilities/spelling.lt).

<a id="facts.capability-grants"></a>
A dependency's `may` ([packages.grants](04-programs.md#packages.grants)) lists effects and capabilities, and each one grants the following:

- `io` grants every capability, and `io` without one;
- each of the eight capabilities grants itself;
- `unsafe` grants C code ([c.granting-unsafe](20-builds.md#c.granting-unsafe)).

Any other string, a string listed twice, and `io` listed with a capability are each E0600, *malformed manifest*.

Tests: [capabilities/grants](../conformance/capabilities/grants/), [capabilities/malformed](../conformance/capabilities/malformed/), [packages/grant_values](../conformance/packages/grant_values/).

<a id="facts.own-capabilities"></a>
A package's own code has a capability when it names a function of another package, `std` included, that has the capability. Names are counted as [packages.own-effects](04-programs.md#packages.own-effects) counts them. The function named is a native of [facts.capability-natives](#facts.capability-natives), or a function whose capabilities, inferred in its own package, include the capability. The package's own code performs `io` without a capability when it names a function of another package whose declared row holds `io` and that has no capability. Calls through function values add nothing. Test bodies, doc examples, properties and bodies with errors don't count.

Tests: [capabilities/closure](../conformance/capabilities/closure/), [capabilities/grants](../conformance/capabilities/grants/), [capabilities/own_impl](../conformance/capabilities/own_impl/), [capabilities/ungranted](../conformance/capabilities/ungranted/), [packages/ungranted_trait](../conformance/packages/ungranted_trait/).

<a id="facts.ungranted-capabilities"></a>
A dependency whose own code has a capability that its entry doesn't grant is E0608, *effect that the manifest doesn't grant*, at its entry. There is one E0608 for each such capability. There is one more for `io` when the dependency's code performs `io` without a capability and its entry doesn't grant `io`. The message names the first function that has it, with the call that causes it ([packages.ungranted-effects](04-programs.md#packages.ungranted-effects)). It offers the narrowest grant: the capabilities that the dependency's own code has, in the order of [facts.capabilities](#facts.capabilities), and `io` alone when the code performs `io` without one. When `run` runs such a program, each function of the dependency whose own code has an ungranted capability is code with an error ([packages.running-with-ungranted-effect](04-programs.md#packages.running-with-ungranted-effect)).

Tests: [capabilities/own_impl](../conformance/capabilities/own_impl/), [capabilities/ungranted](../conformance/capabilities/ungranted/).

## Verification

<a id="facts.verification"></a>
**Verification**, part of `stilt check`, proves operations safe from each body alone. The bodies are those of functions, tests, doc examples, constants and closure literals, and the body of each operation of a handler literal. Verification reads the signatures and declarations of the items a body names, and never another body. It proves in two ways:

- the **rules of acceptance** read the body's text and decide what the limits accept ([facts.rules-of-acceptance](#facts.rules-of-acceptance));
- the **analysis** follows the body's integer values and proves what release builds read ([facts.terms](#facts.terms)).

Either way proves these operations:

- an element read or write of a list or an array, which then can't panic with `bounds`;
- an integer division or remainder, which then can't panic with `divide-by-zero`;
- a read of `m[k]`, which then can't panic with `missing-key`.

The analysis alone also proves arithmetic, shifts and signed divisions that can't overflow ([facts.proved-overflow](#facts.proved-overflow)). No other panic is ever proved, `assert`, `unreachable`, `explicit`, `hole` and `utf8-boundary` among them, and no operation on a `str` is.

Tests: [verification/divisors.lt](../conformance/verification/divisors.lt), [verification/guards.lt](../conformance/verification/guards.lt), [verification/keys.lt](../conformance/verification/keys.lt), [verification/range_loops.lt](../conformance/verification/range_loops.lt).

<a id="facts.what-proofs-change"></a>
An operation that a rule of acceptance proves adds no `panic` ([effects.panicking-operations](12-effects.md#effects.panicking-operations)). A counting loop, and the self-calls of a function that shrink, add no `div` ([facts.div](#facts.div)). The limits read these facts as they read any: `without panic` accepts the operation, `without div` accepts the loop, and a caller that names the function inherits neither. What the analysis alone proves changes no fact: it only lets release builds drop checks.

A proof never adds a fact, and nothing a program does depends on one. A proved check can't fail, so a debug build and the reference interpreter, which keep every check, behave as a release build that drops it. A package's API reads `panic` and `div` as they are when nothing is proved ([versions.facts-without-proofs](21-versions.md#versions.facts-without-proofs)).

Tests: [verification/counting_loops.lt](../conformance/verification/counting_loops.lt), [verification/divisors.lt](../conformance/verification/divisors.lt), [verification/guards.lt](../conformance/verification/guards.lt), [verification/keys.lt](../conformance/verification/keys.lt), [verification/range_loops.lt](../conformance/verification/range_loops.lt), [verification/recursion.lt](../conformance/verification/recursion.lt).

## The rules of acceptance

<a id="facts.rules-of-acceptance"></a>
There are six **rules of acceptance**:

- the **range loop** ([facts.range-loops](#facts.range-loops));
- the **guard** ([facts.guards](#facts.guards));
- the **divisor** ([facts.divisors](#facts.divisors));
- the **key** ([facts.keys](#facts.keys));
- the **counting loop** ([facts.counting-loops](#facts.counting-loops));
- **shrinking recursion** ([facts.shrinking-recursion](#facts.shrinking-recursion)).

They read a body's text, the names it binds and their types, and never the analysis's facts. Each is a shape of code with a name, which E0204 and `stilt show` print ([facts.closest-rule](#facts.closest-rule), [facts.shown-proofs](#facts.shown-proofs)). So a body's size, the joins of its branches and the visits of its loops change nothing that they accept. They use the words that [facts.acceptance-places](#facts.acceptance-places), [facts.known-signs](#facts.known-signs) and [facts.guarding-tests](#facts.guarding-tests) define.

Tests: [verification/counting_loops.lt](../conformance/verification/counting_loops.lt), [verification/counting_loops_held_rejected.lt](../conformance/verification/counting_loops_held_rejected.lt), [verification/counting_loops_rejected.lt](../conformance/verification/counting_loops_rejected.lt), [verification/divisors.lt](../conformance/verification/divisors.lt), [verification/divisors_rejected.lt](../conformance/verification/divisors_rejected.lt), [verification/guards.lt](../conformance/verification/guards.lt), [verification/guards_held_rejected.lt](../conformance/verification/guards_held_rejected.lt), [verification/guards_in_conditions.lt](../conformance/verification/guards_in_conditions.lt), [verification/guards_rejected.lt](../conformance/verification/guards_rejected.lt), [verification/keys.lt](../conformance/verification/keys.lt), [verification/keys_rejected.lt](../conformance/verification/keys_rejected.lt), [verification/large.lt](../conformance/verification/large.lt), [verification/order_effects_rejected.lt](../conformance/verification/order_effects_rejected.lt), [verification/order_rejected.lt](../conformance/verification/order_rejected.lt), [verification/range_arrays.lt](../conformance/verification/range_arrays.lt), [verification/range_arrays_rejected.lt](../conformance/verification/range_arrays_rejected.lt), [verification/range_loops.lt](../conformance/verification/range_loops.lt), [verification/range_loops_rejected.lt](../conformance/verification/range_loops_rejected.lt), [verification/recursion.lt](../conformance/verification/recursion.lt), [verification/recursion_rejected.lt](../conformance/verification/recursion_rejected.lt).

<a id="facts.acceptance-places"></a>
The rules of acceptance name what code writes in these words:

- **Places.** A **place** is a binding's name with any fields after it, as `xs` or `g.cells`, whose binding isn't one that a `when` names ([shared.names-that-may-be-one-place](14-tasks.md#shared.names-that-may-be-one-place)).
- **Changing a length.** Code **changes the length** of the list at a place `P` when it does one of these to `P` or to a place that `P` extends:
  - assigns it;
  - passes it `inout`, as an argument or as the receiver of a method whose `self` is `inout`, such as `push`, `pop`, `clear` or `insert`;
  - yields it from a projection ([projections.yield](13-modes.md#projections.yield)).

  A write through an element, as `P[j] = v` or `P[j].n += v`, doesn't change the length. An array's length never changes.

- **Writing a binding.** Code **writes** a binding when it assigns it, modifies it, as `i += 1` does, or passes it `inout`. A closure literal's body writes only its own copies of what it captures ([expressions.capture](08-expressions.md#expressions.capture)). So code inside a closure literal writes nothing of the body around it.

Tests: [verification/counting_loops_held_rejected.lt](../conformance/verification/counting_loops_held_rejected.lt), [verification/guards_held_rejected.lt](../conformance/verification/guards_held_rejected.lt), [verification/guards_on_fields.lt](../conformance/verification/guards_on_fields.lt), [verification/guards_rejected.lt](../conformance/verification/guards_rejected.lt), [verification/range_loops_rejected.lt](../conformance/verification/range_loops_rejected.lt).

<a id="facts.known-signs"></a>
The rules of acceptance know the signs of some integer expressions:

- **Literal constants.** A **literal constant** is a constant item, or a constant of an inherent impl, whose value is written as an integer literal, with or without a `-`. It stands for that number wherever it is named. Its value is part of its declaration ([generics.constant-arguments](07-types.md#generics.constant-arguments)), so an edit of the value is an edit of a declaration. No other constant is a literal constant, not even a trait's constant where its impl is known.
- **Known non-negative.** An integer expression is **known non-negative** when it is one of these:
  - a non-negative literal or literal constant;
  - a call of `len()`;
  - the variable of a `for` over a range whose start is known non-negative;
  - a `+` or a `*` of known non-negative expressions;
  - a name of a binding whose initial value is known non-negative, and that the body writes only by `=` or `+=` of known non-negative expressions.

  The bindings that the last case defines may count on one another and on themselves. So `n = n + 1` keeps `n` known non-negative, as `n += 1` does.

- **Known positive.** An integer expression is **known positive** when it is a positive literal or literal constant, or the variable of a `for` over a range whose start is one.

Tests: [verification/divisors.lt](../conformance/verification/divisors.lt), [verification/guards.lt](../conformance/verification/guards.lt), [verification/guards_in_conditions.lt](../conformance/verification/guards_in_conditions.lt), [verification/guards_rejected.lt](../conformance/verification/guards_rejected.lt), [verification/known_signs.lt](../conformance/verification/known_signs.lt), [verification/known_signs_rejected.lt](../conformance/verification/known_signs_rejected.lt).

<a id="facts.guarding-tests"></a>
The rules of acceptance read tests and what lies between a test and an operation:

- **Tests.** A **test** gives its facts to the code it guards:
  - the condition of an `if` gives its facts to the `if`'s then-branch;
  - the condition's negation gives its facts to the `else` branch;
  - when each path of the then-branch ends in `return`, `break`, `continue`, `raise` or a call of type `Never`, the negation also gives its facts to the code after the `if` in its block;
  - the condition of a `while` gives its facts to the loop's body.

  Within a condition, the left operand of `&&` gives its facts to the right one, and the left operand of `||` gives its negation's. So `i >= 0 && i < xs.len() && xs[i] > 0` and `i < 0 || i >= xs.len() || xs[i] == 0` are guarded. A condition gives each conjunct of its `&&` chain, read through `!` and parentheses, and its negation gives the negation of each disjunct of its `||` chain. So `if i < 0 || i >= xs.len() { return 0 }` gives `i >= 0` and `i < xs.len()` to the code after it.

- **Between.** Code is **between** a test or a statement and an operation when it is one of these:
  - code that the test guards, or that comes after the statement in its block, and that comes before the statement that holds the operation;
  - code in a loop there that holds the operation;
  - code in the statement that holds the operation, apart from the operation itself.

  The condition of an `if` or a `while` counts as a statement of its own. So the body of `while i < xs.len() && xs[i] == 0 { i += 1 }` isn't between its test and its index.

Tests: [verification/divisors_after_jumps.lt](../conformance/verification/divisors_after_jumps.lt), [verification/divisors_after_jumps_rejected.lt](../conformance/verification/divisors_after_jumps_rejected.lt), [verification/guards.lt](../conformance/verification/guards.lt), [verification/guards_in_conditions.lt](../conformance/verification/guards_in_conditions.lt), [verification/guards_on_fields.lt](../conformance/verification/guards_on_fields.lt), [verification/guards_rejected.lt](../conformance/verification/guards_rejected.lt), [verification/order_effects_rejected.lt](../conformance/verification/order_effects_rejected.lt), [verification/order_rejected.lt](../conformance/verification/order_rejected.lt).

<a id="facts.range-loops"></a>
In the body of a `for i in a..b`, outside its closure literals, an access `P[e]` of a list or an array is proved when all of these hold:

- `e` is `i`, `i + k` or `i - k`, with `k` a non-negative literal or literal constant;
- for `i` and `i + k`, `a` is known non-negative, and for `i - k`, `a` is a literal or a literal constant at least `k`;
- `b` is `P.len()`, or, for `i + k`, `P.len() - c` with `c` a literal or a literal constant at least `k`; for an array of type `Array<T, n>`, `n` may stand for `P.len()`;
- the loop's body doesn't change the length of the list at `P`.

An access of an array by a literal or a literal constant at least 0 and below its size is proved too, in any code.

Tests: [verification/large.lt](../conformance/verification/large.lt), [verification/range_arrays.lt](../conformance/verification/range_arrays.lt), [verification/range_arrays_rejected.lt](../conformance/verification/range_arrays_rejected.lt), [verification/range_loops.lt](../conformance/verification/range_loops.lt), [verification/range_loops_rejected.lt](../conformance/verification/range_loops_rejected.lt), [verification/range_offsets.lt](../conformance/verification/range_offsets.lt).

<a id="facts.guards"></a>
An access `P[e]` of a list or an array is proved when all of these hold:

- `e` is a name of an integer binding, or a non-negative literal or literal constant;
- tests that give `e >= 0`, or `0 <= e`, guard the access, unless `e` is known non-negative;
- tests that give `e < P.len()`, or `P.len() > e`, guard the access;
- nothing between those tests and the access writes `e`'s binding or changes the length of the list at `P`.

For `e` the literal 0, `!P.is_empty()` gives `0 < P.len()`.

Tests: [generics/array_effects.lt](../conformance/generics/array_effects.lt), [verification/guards.lt](../conformance/verification/guards.lt), [verification/guards_held_rejected.lt](../conformance/verification/guards_held_rejected.lt), [verification/guards_in_conditions.lt](../conformance/verification/guards_in_conditions.lt), [verification/guards_on_fields.lt](../conformance/verification/guards_on_fields.lt), [verification/guards_rejected.lt](../conformance/verification/guards_rejected.lt), [verification/known_signs.lt](../conformance/verification/known_signs.lt), [verification/known_signs_rejected.lt](../conformance/verification/known_signs_rejected.lt), [verification/order_effects_rejected.lt](../conformance/verification/order_effects_rejected.lt), [verification/order_rejected.lt](../conformance/verification/order_rejected.lt), [verification/range_arrays_rejected.lt](../conformance/verification/range_arrays_rejected.lt), [verification/range_offsets.lt](../conformance/verification/range_offsets.lt).

<a id="facts.divisors"></a>
An integer `/`, `%`, `/=` or `%=` is proved not to divide by zero when its divisor is one of these:

- a non-zero literal or literal constant;
- a name of a binding that is known positive;
- a name `d` of a binding that tests guard, with nothing between them and the division writing `d`. The tests give `d != 0`, `d > 0` or `d < 0`, or the mirror of one.

The negation of `d == 0` gives `d != 0`, so `if d == 0 { 0 } else { n / d }` is proved.

Tests: [declarations/function_limits.lt](../conformance/declarations/function_limits.lt), [verification/divisors.lt](../conformance/verification/divisors.lt), [verification/divisors_after_jumps.lt](../conformance/verification/divisors_after_jumps.lt), [verification/divisors_after_jumps_rejected.lt](../conformance/verification/divisors_after_jumps_rejected.lt), [verification/divisors_rejected.lt](../conformance/verification/divisors_rejected.lt), [verification/known_signs.lt](../conformance/verification/known_signs.lt), [verification/known_signs_rejected.lt](../conformance/verification/known_signs_rejected.lt).

<a id="facts.keys"></a>
An access `m[k]` of a map, other than the store of `m[k] = v`, is proved when all of these hold:

- `k` is a name of a binding, or a literal that doesn't interpolate;
- `k`'s type isn't a type parameter, and its `Eq` and `Hash` are a primitive type's, or structural throughout its parts ([traits.structural-impls](11-traits.md#traits.structural-impls));
- the access is guarded or preceded in one of these ways:
  - a test that gives `m.contains(k)` guards it;
  - a statement `m[k] = v` or `m.insert(k, v)` comes before it, in its block or in a block around it;
  - an `if` whose condition is `!m.contains(k)`, and whose then-branch ends with such a statement, comes before it there;
- nothing between that test or statement and the access writes `k`, or changes `m` other than by storing into it.

`m[j] = v`, `m.insert(j, v)` and a write through `m[j]` store into `m`. Every other change, as `m.remove(j)`, `m.clear()`, an assignment of `m` or passing `m` `inout`, doesn't. So `if !m.contains(k) { m[k] = 0 }` followed by `m[k] += 1` is proved.

Tests: [verification/keys.lt](../conformance/verification/keys.lt), [verification/keys_rejected.lt](../conformance/verification/keys_rejected.lt), [verification/order_effects_rejected.lt](../conformance/verification/order_effects_rejected.lt), [verification/order_rejected.lt](../conformance/verification/order_rejected.lt), [verification/range_offsets.lt](../conformance/verification/range_offsets.lt).

<a id="facts.counting-loops"></a>
A `while` ends, and adds no `div`, when its condition compares a name `v` and an expression `b` and all of the rules below hold. The comparison is by `<`, `<=`, `>` or `>=`, and it is the whole condition or the first conjunct of an `&&` chain.

- `v` names a `var` of an integer type, the loop's **counter**.
- `b`, its **bound**, is made of literals, constants, names of bindings that the body doesn't write, and calls `P.len()` of places whose length the body doesn't change, by `+`, `-` and `*`.
- The body holds a step of `v` as a statement of its own block, not inside an `if`, a `match`, a loop or a closure. The step is `v += s` where the comparison asks `v` to grow toward `b`, as `v < b` and `b > v` do. It is `v -= s` where the comparison asks `v` to shrink. `s` is known positive, or is a name of a binding that the body doesn't write and that is known positive.
- No `continue` of the loop comes before that statement, and the body writes `v` nowhere else.

A `break` may come anywhere. Every other `while`, and every `loop`, adds `div` ([facts.div](#facts.div)).

Tests: [promises/termination_rejected.lt](../conformance/promises/termination_rejected.lt), [verification/counting_loops.lt](../conformance/verification/counting_loops.lt), [verification/counting_loops_held_rejected.lt](../conformance/verification/counting_loops_held_rejected.lt), [verification/counting_loops_rejected.lt](../conformance/verification/counting_loops_rejected.lt), [verification/guards_in_conditions.lt](../conformance/verification/guards_in_conditions.lt).

<a id="facts.shrinking-recursion"></a>
A function's self-calls **shrink** when, for one `let` parameter `p` of an integer type, every self-call in its body passes the same one of these at `p`'s position:

- `p - s`, under a test that gives `p > b` or `p >= b`, or the mirror of one;
- `p + s`, under a test that gives `p < b` or `p <= b`, or the mirror of one.

Here `s` is known positive. `b` is a literal, a literal constant, or another `let` parameter that every self-call passes unchanged at its own position. The test guards the call as [facts.guarding-tests](#facts.guarding-tests) says. So `if n <= 0 { 0 } else { count(n - 1) }` shrinks, and `if n == 0 { 0 } else { count(n - 1) }` doesn't, and neither does `if p > 5 { f(p - 1) } else if p < 10 { f(p + 1) } else { 0 }`, whose self-calls step both ways. A function whose self-calls all shrink, or all descend ([facts.descending-self-calls](#facts.descending-self-calls)), adds no `div` at them. A function whose self-calls mix the two adds `div`, and so does mutual recursion.

Tests: [promises/termination_rejected.lt](../conformance/promises/termination_rejected.lt), [verification/recursion.lt](../conformance/verification/recursion.lt), [verification/recursion_rejected.lt](../conformance/verification/recursion_rejected.lt).

<a id="facts.closest-rule"></a>
When a limit rejects an operation that no rule of acceptance proves, its E0204 says which rule comes closest and what that rule needs. It says so beside the limit and the line, in the source's own text. For example, the message ``This index can panic, but the module's header says `without panic` `` has the help ``A guard needs a test that gives `i < xs.len()`.`` The closest rule is:

- the range loop, for an index that names the variable of a `for` over a range around it;
- the guard, for every other index;
- the divisor, for a division;
- the key, for a map's key;
- the counting loop, for a `while`;
- shrinking recursion, for a self-call.

What the rule needs is the first of its conditions, in the order of its paragraph, that the code doesn't meet:

- **Range loop:** `a range loop needs the index to be i, i + k or i - k`; `a range loop needs it to start at a value known non-negative`, or `at k or above`; `a range loop needs it to end at xs.len(), not at n`; `a range loop needs the index outside closures`; `a range loop needs a body that keeps the length of xs, which line 6 changes`.
- **Guard:** `a guard needs the index to be a name or a literal`; `a guard needs a test that gives i >= 0`, then `… i < xs.len()`; `a guard needs nothing between the test and the index to write i, which line 4 does`, or `… to change the length of xs, which line 4 does`.
- **Divisor:** `a divisor needs to be a name or a literal other than 0`; `a divisor needs a test that gives d != 0`; `a divisor needs nothing between the test and the division to write d, which line 4 does`.
- **Key:** `a key needs to be a name or a literal that doesn't interpolate`; `a key needs a type whose Eq and Hash are structural`; `a key needs a test that gives counts.contains(item), or a store of item before it`; `a key needs nothing between to change counts but by storing into it, which line 4 does`, or `… to write item, which line 4 does`.
- **Counting loop:** `a counting loop needs a comparison by <, <=, > or >=`; `a counting loop needs a var on one side`; `a counting loop needs a bound that the loop doesn't change, which line 5 does`; `a counting loop needs a statement i += s of the loop's own block, with s known positive`; `a counting loop needs no continue before i += 1, which line 4 is`; `a counting loop needs i written nowhere else, which line 6 does`.
- **Shrinking recursion:** `shrinking recursion needs every self-call to pass p - s or p + s at one parameter`; `shrinking recursion needs a test that gives n > b at the self-call on line 3`.

Where the expression's type allows it, the fix for an index reads the element through `get`, which can't panic. The fix for a key reads it through `get` with a default.

Tests: [verification/counting_loops_rejected.lt](../conformance/verification/counting_loops_rejected.lt), [verification/divisors_rejected.lt](../conformance/verification/divisors_rejected.lt), [verification/guards_rejected.lt](../conformance/verification/guards_rejected.lt), [verification/keys_rejected.lt](../conformance/verification/keys_rejected.lt), [verification/order_rejected.lt](../conformance/verification/order_rejected.lt), [verification/range_arrays_rejected.lt](../conformance/verification/range_arrays_rejected.lt), [verification/range_loops_rejected.lt](../conformance/verification/range_loops_rejected.lt), [verification/recursion_rejected.lt](../conformance/verification/recursion_rejected.lt).

Checked by: also the snapshots of E0204 in `tests/diagnostics/`, which `just diagnostics` checks.

<a id="facts.shown-proofs"></a>
`stilt show` and the language server print `proved bounds`, `proved divide-by-zero` and `proved missing-key` in a function's bracket after its signature. They also print them at each line where a rule of acceptance proves a check, where a `panic` would have been. There each is followed by the rule's name, as `proved bounds by a range loop`. `show --json` gives each one's rule under `rule`. A counting loop shows no `div`. What the analysis alone proves isn't printed at its line, and neither is a proved overflow. `stilt show --release` counts, for each function, the checks that release builds drop and those they keep ([builds.performance-report](20-builds.md#builds.performance-report)).

Checked by: the facts suite, whose `PROVED` annotations, with near misses that keep `PANIC`, `just facts` checks, and the toolchain's tests of `stilt show` (`compiler/stilt-cli/tests/show.rs`).

## The analysis

<a id="facts.terms"></a>
The analysis of a body follows integer values, its **terms**. A term stands for one value each time the code that makes it runs. So a fact on a term holds until a path takes it back to a loop's head. There, the head terms, and the terms the body makes, stand for one iteration's values ([facts.loop-heads](#facts.loop-heads)). The terms are:

- **Bindings.** Each binding of an integer type that the body declares has a term for each value it takes. Such a binding is a parameter, a `let` or `var` binding, or a binding of a pattern. Its **current** term at a point is the term of the value it holds there. An assignment gives it a new one ([facts.bindings-and-assignments](#facts.bindings-and-assignments)), and so does a call that takes it `inout` ([facts.writes-through-calls](#facts.writes-through-calls)). In a closure literal's body or an operation's body, each binding that it captures has one term, with its type's bounds only.
- **Lengths.** Each binding of a list that the body declares or captures has a term for each length it takes. The current one is its current length, written `len(xs)` below. Each change of its length gives it a new one.
- **Sizes.** An array's size is a term when it is a value parameter, and a number when it is a literal or a constant ([generics.array-sizes](07-types.md#generics.array-sizes)).
- **Value parameters.** Each value parameter of an integer type in scope ([generics.value-parameters-in-body](07-types.md#generics.value-parameters-in-body)) is a term.
- **Values.** The value of an integer expression that has no linear form ([facts.linear-forms](#facts.linear-forms)) is a new term as it is evaluated, with its interval and relative bounds as its facts.
- **Loops and joins.** A `for` over a range has a counter and two bounds ([facts.for-loops](#facts.for-loops)). A loop's head and a join give new terms to what their paths change ([facts.joins](#facts.joins), [facts.loop-heads](#facts.loop-heads)).
- **Zero.**

A `let` or a `var` declares a new binding, so `let i = i - 1` gives the new `i` terms of its own, apart from the old one's. A literal constant ([facts.known-signs](#facts.known-signs)) stands for its number wherever it is named. A field, an element, a map's value, a call's result and every other constant have no term of their own. Their values are values without a linear form. The bindings that a `when` names ([shared.names-that-may-be-one-place](14-tasks.md#shared.names-that-may-be-one-place)) have no terms, no lengths and no versions. An expression that names one has no linear form, and its value is a new term with its type's bounds.

Tests: [verification/analysis.lt](../conformance/verification/analysis.lt).

<a id="facts.difference-facts"></a>
A **difference fact** is `t − u ≤ c`, for terms `t` and `u` and an integer `c`. With `u` zero it bounds `t` from above, and with `t` zero from below. Every `c` is an exact integer, of no fixed width: a `u64` term against an `i64` one needs 66 bits. The analysis's facts at a point are:

- a set of difference facts, at most one for each ordered pair of terms, kept **closed**. In a closed set, whenever `t − u ≤ c` and `u − v ≤ d` hold, `t − v ≤ c + d` holds. Of two facts on one pair, the smaller `c` holds;
- which terms are **non-zero**. Closing a set applies these too: a non-zero term bounded below by 0 is bounded below by 1, and one bounded above by 0 is bounded above by −1. Closure repeats until nothing changes;
- which keys of which maps are **present** ([facts.map-keys](#facts.map-keys)).

A set in which some `t − t ≤ c` has `c < 0` is **contradictory**. Its point is never reached, and it takes no part in a join or a widening. The term of a binding's value lies within the bounds of the binding's type. A counter has no type, and no bounds but its loop's ([facts.for-loops](#facts.for-loops)). A length lies between 0 and 2^48 ([facts.greatest-length](#facts.greatest-length)), and so does an array's size wherever a binding of its type has a value.

At the end of each statement, once the set is closed, every term is dropped that is none of these:

- a binding's current term, length or version;
- a key's term;
- a value that the evaluation has read and not yet used.

Every implementation drops the same terms at the same points.

Tests: [verification/analysis.lt](../conformance/verification/analysis.lt).

<a id="facts.greatest-length"></a>
No list or array holds more than 2^48 elements. In every implementation, an operation that would make a longer one ends the program as running out of memory does, with status 134 ([program.exit-statuses](04-programs.md#program.exit-statuses)). An array may end a run sooner ([generics.large-arrays](07-types.md#generics.large-arrays)). So two indexes in range add without overflow.

Checked by: each implementation's own tests, as the reference interpreter's `interpreter/test/test_lengths.ml`, since no conformance test makes such a list: 2^48 pushes take days.

<a id="facts.linear-forms"></a>
An integer expression's value is a **linear form**, a term plus a number, when the expression is one of these:

- a literal or a literal constant: zero plus its value;
- a binding of an integer type: its current term plus 0;
- a value parameter of an integer type in scope: its term plus 0;
- `xs.len()`, for `xs` a binding of a list: its current length plus 0;
- `e.len()`, where `e` has the type `Array<T, n>` and is a place, a binding with fields and indexes after it, whose indexes are linear forms: `n`'s term plus 0, or zero plus `n` when `n` is a number;
- `e + c`, `c + e` or `e - c`, for `e` of a linear form `t + d` and `c` a literal or a literal constant: `t` plus `d + c`, or `t` plus `d − c`;
- `(e)`, for `e` of a linear form;
- `x.to_T()`, for `x` of a linear form, when its result type is `T` and not an `Option` ([numbers.conversions](06-numbers.md#numbers.conversions)): `x`'s form.

No expression of a linear form assigns anything, so evaluating one changes no fact. The form names the terms that are current where it is evaluated, so a later assignment leaves the value it gave as it was.

Tests: [verification/analysis.lt](../conformance/verification/analysis.lt), [verification/order_block_length.lt](../conformance/verification/order_block_length.lt), [verification/order_shifted.lt](../conformance/verification/order_shifted.lt).

<a id="facts.intervals"></a>
Every integer expression has an **interval**: the least and greatest values that the facts allow it at the end of its evaluation, computed from its parts.

- A linear form's interval comes from the facts on its term.
- `a + b`, `a - b`, `a * b` and `-a` take the exact results of their operands' intervals, then are cut to the type's bounds.
- For `a / b` and `a % b`, take `a`'s interval to be `al` to `ah`, and the divisor's to be `bl` to `bh` with `bl ≥ 1`. Division truncates toward zero ([numbers.division-and-remainder](06-numbers.md#numbers.division-and-remainder)).
  - When `al ≥ 0`, `a / b` lies between `al / bh` and `ah / bl`.
  - Otherwise, the least value of `a / b` is `al / bl`, and its greatest is `ah / bl` when `ah ≥ 0`, and `ah / bh` otherwise.
  - `a % b` lies between `max(al, 1 − bh)` and `min(ah, bh − 1)`. Its least value is 0 when `al ≥ 0`, and its greatest is 0 when `ah ≤ 0`.
- Any other divisor's quotient or remainder, and any other expression, a call's result among them, has its type's bounds.

Tests: [verification/analysis.lt](../conformance/verification/analysis.lt), [verification/order_block_length.lt](../conformance/verification/order_block_length.lt), [verification/order_shifted.lt](../conformance/verification/order_shifted.lt).

<a id="facts.relative-bounds"></a>
Some forms that have no linear form give **relative bounds** too: facts between their value's term `v` and the terms of their operands' values.

- `a + b`: for each operand whose value is a linear form `t + d`, with the other's interval `l` to `h`, `d + l ≤ v − t ≤ d + h`.
- `a - b`, with `a`'s value `t + d` and `b`'s interval `l` to `h`: `d − h ≤ v − t ≤ d − l`. So `k += i`, with `i` at least 2, makes the new `k` at least the old one plus 2.
- `a % b`, where `a` is proved at least 0 and `b`'s value is a linear form `t + c` proved at least 1, is less than `b`. So `xs[h % xs.len()]` is in range when `h ≥ 0` and `xs` isn't empty.
- When `a` and `b` are linear forms and `a ≤ b` is proved, `a + (b - a) / c` lies between `a` and `b`, for `c` a literal at least 2. So does `(a + b) / 2`, when `a` is proved at least 0. Each lies below `b` when `a < b` is proved. This covers the middle of a binary search.

Tests: [verification/analysis.lt](../conformance/verification/analysis.lt), [verification/order_block_length.lt](../conformance/verification/order_block_length.lt), [verification/order_shifted.lt](../conformance/verification/order_shifted.lt).

<a id="facts.analysis-order"></a>
The analysis's facts flow through a body in the order of evaluation ([values.left-to-right](05-values.md#values.left-to-right), [values.assignment-order](05-values.md#values.assignment-order), [values.compound-assignment-order](05-values.md#values.compound-assignment-order)). Each operation is checked with the values it uses, as they were evaluated, and the facts where it happens:

- a read `xs[e]`: the length that `xs` had where `xs` was evaluated, which is before `e` ([values.index-reads](05-values.md#values.index-reads)), against `e`'s value;
- a store `xs[e] = v`, `xs[e].f = v` or `xs[e][j] = v`, and a compound assignment through `xs[e]`: the length current after `v` is evaluated;
- an `inout` argument or an `inout self` receiver whose place goes through `xs[e]`: the length current where the call starts, before its changes of [facts.writes-through-calls](#facts.writes-through-calls). For a projection's call, it is the length current where its access starts ([projections.when-projection-runs](13-modes.md#projections.when-projection-runs));
- a call of a function of the table of [facts.proved-indexes](#facts.proved-indexes): its arguments' values, against the receiver's length where the receiver is read. For `slice`, which takes `self`, that is where the receiver is evaluated. For `insert`, `remove` and `swap`, which take `inout self`, it is where the call starts ([modes.durations](13-modes.md#modes.durations)).

So `xs[i] = { i = 0; 1 }` checks the value that `i` had when the index was evaluated. `xs[0] = { xs.clear(); 1 }` checks the length after `clear`, and `xs[{ xs.push(0); 3 }]` checks the length before the `push`.

Tests: [verification/analysis.lt](../conformance/verification/analysis.lt), [verification/order_argument_cleared.lt](../conformance/verification/order_argument_cleared.lt), [verification/order_block_length.lt](../conformance/verification/order_block_length.lt), [verification/order_field_cleared.lt](../conformance/verification/order_field_cleared.lt), [verification/order_inserted.lt](../conformance/verification/order_inserted.lt), [verification/order_read_pushed.lt](../conformance/verification/order_read_pushed.lt), [verification/order_store_cleared.lt](../conformance/verification/order_store_cleared.lt), [verification/order_store_index.lt](../conformance/verification/order_store_index.lt), [verification/order_swapped.lt](../conformance/verification/order_swapped.lt).

<a id="facts.bindings-and-assignments"></a>
Bindings take their terms and lengths as follows:

- **Integers.** At `let x = e`, `var x = e` or `x = e`, for `x` a binding of an integer type, `x`'s current term becomes `e`'s value. For a value without a linear form, that is the value's term. For a linear form `u + c`, it is a new term `t` with `t − u ≤ c` and `u − t ≤ −c`. A new term is non-zero when its interval leaves out zero, or when the value is a non-zero term plus 0.
- **Compound assignments.** `x op= e` is `x = x op v`, with `x`'s value read after `e` is evaluated, for `v` the value that `e` gave ([values.compound-assignment-order](05-values.md#values.compound-assignment-order)).
- **Patterns and loops.** A binding of a pattern, and the variable of a `for` over a list or a map, has a new term with its type's bounds only. The literal patterns of [facts.match-arms](#facts.match-arms) are the exception.
- **Lists.** At `let xs = e`, `var xs = e` or `xs = e`, for `xs` a binding of a list, `xs` gets a new length:
  - for a list literal with no spread, the number of its elements;
  - for `List.new()`, 0;
  - for `e` naming a list binding `ys` whole, the current length of `ys`;
  - for `List.repeat(x, n)`, where `n`'s value is a linear form proved at least 0, `n`'s value.

  Every other expression gives the new length its bounds of [facts.difference-facts](#facts.difference-facts) only.

Tests: [verification/analysis.lt](../conformance/verification/analysis.lt), [verification/order_shifted.lt](../conformance/verification/order_shifted.lt).

<a id="facts.writes-through-calls"></a>
A closure captures by copy ([expressions.capture](08-expressions.md#expressions.capture)). So no call changes a binding of its caller but one that it takes `inout`. A call that takes a list binding `xs` `inout`, as its receiver or an argument, gives `xs` a new length `ℓ'`, from its length `ℓ` where the call starts:

| Call | `ℓ'` |
| --- | --- |
| `xs.push(x)`, `xs.insert(i, x)` | `ℓ + 1` |
| `xs.remove(i)` | `ℓ − 1` |
| `xs.pop()` | `ℓ − 1` where `ℓ ≥ 1` is proved; otherwise at least 0 and at most `ℓ` |
| `xs.clear()` | 0 |
| `xs.swap(i, j)`, and an assignment through `xs[i]` | `ℓ`, and no new length |

Every other call that takes `xs` `inout`, and every `inout` argument that names `xs` or a place inside it, gives `xs` a new length with its bounds only. `yield p` in a projection lends `p` to the caller, as such a call does ([projections.yield](13-modes.md#projections.yield)). When `p`'s root is a list binding, it gets a new length with its bounds only. When `p`'s root is an integer binding, it gets a new term with its bounds only. A call that takes an integer binding `inout` gives it a new term with its type's bounds only.

Tests: [verification/analysis.lt](../conformance/verification/analysis.lt), [verification/order_guarded.lt](../conformance/verification/order_guarded.lt), [verification/order_matched_pop.lt](../conformance/verification/order_matched_pop.lt), [verification/order_yielded.lt](../conformance/verification/order_yielded.lt).

<a id="facts.conditions"></a>
A condition gives facts where it is true and where it is false, on the values it compares:

- **Comparisons.** `a < b`, `a <= b`, `a > b`, `a >= b` and `a == b`, on integers whose values are linear forms, give the difference facts they state where true. Where false, they give the facts that their negations state. `a < b` states `a − b ≤ −1`, and `a == b` states `a − b ≤ 0` and `b − a ≤ 0`.
- **Non-zero.** `a != b` where true, and `a == b` where false, make the term `t` non-zero when `a`'s value is `t + 0` and `b` is the literal 0. The mirror holds too. Where `a != b` is false, it gives what `a == b` gives where true.
- **Calls.** `xs.is_empty()` is `xs.len() == 0`, and `m.contains(k)` makes the key present where it is true ([facts.map-keys](#facts.map-keys)).
- **Connectives.** `!c` swaps where `c` is true and false. In `a && b`, `b` starts with `a`'s facts where `a` is true. `a && b` gives `b`'s facts where `b` is true. Where it is false, it gives the facts that `a` false and `b` false both keep ([facts.joins](#facts.joins)). `a || b` is the same, with true and false swapped.

A condition is read this way in an `if`, an `else if`, the head of a `while` and the guard of a `match` arm. Every other condition, and every condition of another type, gives nothing but the facts that its evaluation leaves.

Tests: [verification/analysis.lt](../conformance/verification/analysis.lt), [verification/order_emptied.lt](../conformance/verification/order_emptied.lt).

<a id="facts.joins"></a>
Paths meet after an `if` or a `match`, at the end of a loop, where a `break` leaves a loop, and at the end of a `with`. Where they meet, each binding whose current term, length or version ([facts.map-keys](#facts.map-keys)) differs between the paths takes a new one. On each path, the new one equals that path's own. The facts there are those that every path keeps:

- for each pair of terms, the greatest `c` among the paths', with each path's own terms read as the new ones;
- a new term is non-zero when on every path that path's own term is;
- a key is present at a new version when on every path it is present at that path's own version.

A term or a pair that one path lacks holds no fact. A loop's head terms join the same way ([facts.loop-heads](#facts.loop-heads)).

Tests: [verification/analysis.lt](../conformance/verification/analysis.lt), [verification/order_caught.lt](../conformance/verification/order_caught.lt), [verification/order_ended.lt](../conformance/verification/order_ended.lt), [verification/order_ended_through.lt](../conformance/verification/order_ended_through.lt), [verification/order_guarded.lt](../conformance/verification/order_guarded.lt), [verification/order_matched_pop.lt](../conformance/verification/order_matched_pop.lt), [verification/order_popped_twice.lt](../conformance/verification/order_popped_twice.lt).

<a id="facts.paths-that-leave"></a>
Some paths go elsewhere than to the next statement:

- A path that leaves the body or its loop, by `return`, `raise`, `break`, `continue` or a call of type `Never`, joins only where it goes.
- A call or a performance whose row holds `raise<E>`, under a `try`, goes to its `catch` arms, or out of the body. It goes with the facts after its changes of [facts.writes-through-calls](#facts.writes-through-calls) and [facts.map-keys](#facts.map-keys).
- Inside a `with` whose handler takes control ([handlers.resuming](12-effects.md#handlers.resuming)), the operation that ends it may be performed through another handler's body or a function value ([handlers.call-that-handler-ends](12-effects.md#handlers.call-that-handler-ends)). So each performance of any operation inside it is a path to that `with`'s end, and so is each call inside it whose row holds an effect or a row variable. Each such path carries the facts after its changes.

Tests: [verification/analysis.lt](../conformance/verification/analysis.lt), [verification/order_caught.lt](../conformance/verification/order_caught.lt), [verification/order_ended.lt](../conformance/verification/order_ended.lt), [verification/order_ended_through.lt](../conformance/verification/order_ended_through.lt), [verification/order_guarded.lt](../conformance/verification/order_guarded.lt), [verification/order_matched_pop.lt](../conformance/verification/order_matched_pop.lt), [verification/order_popped_twice.lt](../conformance/verification/order_popped_twice.lt).

<a id="facts.match-arms"></a>
The first arm of a `match` starts with the facts after its scrutinee, whose value is the arms' **scrutinee value**. Each later arm starts with the facts that the earlier arms leave where they fail: those where an earlier pattern doesn't match, and those where an earlier guard is false.

- When the scrutinee value is a linear form `t + d`, an integer literal pattern `c` adds `t = c − d` to its arm. An or-pattern of literals adds the join of what each literal adds. A later arm knows `t + d` non-zero when an arm before it, with no guard, is the literal 0 alone.
- When an arm's pattern holds an or-pattern, its guard may run once for each way it matches ([patterns.guards](09-patterns.md#patterns.guards)). The guard is then the body of a loop ([facts.loop-heads](#facts.loop-heads)), entered with the facts after the pattern. The arm starts with that loop's facts where the guard is true, and the later arms start with its facts where it is false.

A `let … else` is a `match` of its pattern and the `else`.

Tests: [verification/analysis.lt](../conformance/verification/analysis.lt), [verification/order_guarded.lt](../conformance/verification/order_guarded.lt), [verification/order_matched_pop.lt](../conformance/verification/order_matched_pop.lt), [verification/order_popped_twice.lt](../conformance/verification/order_popped_twice.lt).

<a id="facts.loop-heads"></a>
At a loop's head, each binding that the loop assigns, and each length and version that it changes, takes a new term, its **head term**. On each path into the head, the head term equals that path's own. On a path back to the head, the facts are first restricted to the head's terms, read with the path's own terms. Each head term's earlier value is forgotten, and the path's own term then takes its name, with its facts, its being non-zero and the keys present at it. The facts at the head are on these terms only:

- the head terms;
- the current terms, lengths and versions of the bindings in scope;
- the bounds of this loop and of the loops around it;
- the values, lengths and versions that the evaluation around the loop has read and not yet used ([facts.analysis-order](#facts.analysis-order));
- the terms of the enclosing loops' heads;
- the value parameters;
- zero.

The loops inside a loop reach their own heads' facts at each visit of the outer loop ([facts.widening](#facts.widening)).

Tests: [verification/analysis.lt](../conformance/verification/analysis.lt), [verification/order_after_inclusive.lt](../conformance/verification/order_after_inclusive.lt), [verification/order_summed.lt](../conformance/verification/order_summed.lt).

<a id="facts.widening"></a>
A loop's head facts are reached by visiting the loop again until they stop changing:

- **First visit.** It starts with the join ([facts.joins](#facts.joins)) of the facts before the loop.
- **Later visits.** Each later set comes from the join of the facts before the loop with those at the end of the body and at each `continue`. Pair by pair, it is the greater of the last set's `c` and that join's, **widened** where it grew. A pair that grew is widened to the least of the loop's thresholds at least as large, or dropped when none is. From the sixth visit on, a pair that grew is dropped, whatever the thresholds. A later set's non-zero terms and present keys are those of that join that the last set has too. Each visit analyses the body from the closure of that set. The visits stop when a set equals the last one in its difference facts, compared before closure, its non-zero terms and its present keys.
- **Thresholds.** A loop's thresholds are:
  - the integer-typed literals of the loop's text, its head and iterable, its closures, patterns and value arguments included;
  - the values of the literal constants that the loop names;
  - the negation of each of these, and each of these and of their negations plus one and minus one;
  - the least and greatest values of each of the eight integer types;
  - 0 and 2^48.
- **Narrowing.** The head's facts are then the closed join of the facts before the loop with those of one more visit. That visit starts from the closed last set, and its facts are those at the end of the body and at each `continue`. The body and the exits read the visit from these.

Tests: [verification/analysis.lt](../conformance/verification/analysis.lt), [verification/order_after_inclusive.lt](../conformance/verification/order_after_inclusive.lt), [verification/order_summed.lt](../conformance/verification/order_summed.lt).

<a id="facts.for-loops"></a>
A `for` over a range `a..b` is analysed as its bounds, then a loop. The bounds are the values of `a` and `b`, evaluated in that order before the loop ([expressions.range-iteration](08-expressions.md#expressions.range-iteration)). The counter is the loop's head term for its variable. It starts at the first bound and has no type bounds. At the head it is compared with the second bound, as `counter < b`, or `counter <= b` for `a..=b`. It grows by one at the end of the body and at each `continue`. The loop's variable is the counter in each iteration, and its type's bounds apply to it there. So after `for _ in 0..n { xs.push(x) }` on an empty `xs`, `len(xs)` is at least `n`. A `for` over a list or a map is a loop whose variable has its type's bounds.

Tests: [verification/analysis.lt](../conformance/verification/analysis.lt), [verification/order_after_inclusive.lt](../conformance/verification/order_after_inclusive.lt), [verification/order_summed.lt](../conformance/verification/order_summed.lt).

<a id="facts.large-bodies"></a>
A body's count is the sum of these, taken in its own text outside its closure and handler literals:

- its bindings of integer types and its bindings of lists;
- the value parameters in scope;
- three for each `for` over a range, its variable among them;
- one, for zero.

When the count is above 64, each time the analysis adds facts, the set is closed, and every fact between two terms neither of which is zero is then dropped. So each term keeps only its bounds. A closure literal's body and an operation's body are counted on their own, each capture among their bindings.

Tests: [verification/large.lt](../conformance/verification/large.lt).

<a id="facts.proved-indexes"></a>
An access `xs[e]` is proved when the facts at the access ([facts.analysis-order](#facts.analysis-order)) give `0 ≤ ι` and `ι ≤ ℓ − 1`, for `ι` the value of `e`. Here `xs` is a binding of a list, with `ℓ` its length, or an expression of type `Array<T, n>`, with `ℓ` its size. The only panic of these functions of `std` is `bounds` on their arguments. A call of one is proved when the facts give the following, for its arguments' values and `ℓ` the receiver's length:

| Call | Proved when |
| --- | --- |
| `xs.insert(i, x)` | `0 ≤ i ≤ ℓ` |
| `xs.remove(i)` | `0 ≤ i < ℓ` |
| `xs.slice(a, b)` | `0 ≤ a ≤ b ≤ ℓ` |
| `xs.swap(i, j)` | `0 ≤ i < ℓ` and `0 ≤ j < ℓ` |

Tests: [verification/analysis.lt](../conformance/verification/analysis.lt), [verification/order_inserted.lt](../conformance/verification/order_inserted.lt), [verification/order_summed.lt](../conformance/verification/order_summed.lt), [verification/order_swapped.lt](../conformance/verification/order_swapped.lt).

<a id="facts.proved-divisions"></a>
An integer `/`, `%`, `/=` or `%=` is proved not to divide by zero when its divisor's interval leaves out zero. It is proved too when its divisor's value is a non-zero term plus 0.

Tests: [verification/analysis.lt](../conformance/verification/analysis.lt).

<a id="facts.map-keys"></a>
Each binding of a map, and each binding of another type that isn't an integer, has a **version**. The version changes at each modification of the binding or of a place rooted in it ([modes.kinds-of-access](13-modes.md#modes.kinds-of-access)): an assignment, an `inout` argument or an `inout` receiver. It also changes at each `yield` of either ([projections.yield](13-modes.md#projections.yield)). A **key** is one of the following, of a type that isn't a type parameter and whose `Eq` and `Hash` are a primitive type's, or structural throughout its parts ([traits.structural-impls](11-traits.md#traits.structural-impls)):

- a binding of an integer type: its value's linear form where it was evaluated, so two such keys are the same when their forms are;
- a binding of another type, at the version it had where it was evaluated;
- a literal that doesn't interpolate, the same key as another whose text is the same.

A key's `hash` and `eq` perform nothing and give what its value gives ([std.finding-keys](17-std.md#std.finding-keys)), and the names of a `when` have no versions ([facts.terms](#facts.terms)). So such a key is found again once found. Then:

- **Becoming present.** `m[k] = v`, `m.insert(k, v)` and `m.get_or_insert(k, d)` give `m` a new version, at which the keys present at its last are present, and so is `k`. Where `m.contains(k)` is true, `k` is present at `m`'s current version.
- **Staying present.** A compound assignment through `m[k]`, and an assignment or an `inout` argument whose place goes through `m[k]`, as `m[k].n = 0` or `bump(inout m[k])`, give `m` a new version. The keys present at its last version are present at the new one.
- **Ceasing to be present.** Every other change of `m`'s version, a call that takes it `inout` or `m.remove(_)` among them, makes no key present at the new one.
- **Reading.** An access through `m[k]`, other than the store of `m[k] = v`, is proved when `k` is present at `m`'s version where the access happens. [facts.analysis-order](#facts.analysis-order) places the access:
  - for a read, where `m` is evaluated;
  - for an assignment or a compound assignment through `m[k]`, as `m[k].n = v` or `m[k] += v`, after the right side;
  - for an `inout` argument or receiver through `m[k]`, where the call starts.

Tests: [verification/analysis.lt](../conformance/verification/analysis.lt), [verification/order_argument_cleared.lt](../conformance/verification/order_argument_cleared.lt), [verification/order_field_cleared.lt](../conformance/verification/order_field_cleared.lt).

<a id="facts.proved-overflow"></a>
The analysis proves operations that can't overflow:

- `a + b`, `a - b`, `a * b` and `-a`, and their compound assignments, when the interval of the exact result lies within the type's bounds. The interval is the one that [facts.intervals](#facts.intervals) computes before it is cut to those bounds;
- a shift, when its amount's interval lies within 0 and the width less one;
- a signed division or remainder, when its dividend's interval leaves out the type's least value, or its divisor's leaves out −1 ([numbers.integer-panics](06-numbers.md#numbers.integer-panics)).

Overflow is a fact of its own, which no proof removes ([effects.overflow-effect](12-effects.md#effects.overflow-effect)). So a proof of it changes nothing that `check` accepts. Release builds drop the check, and the performance report counts it ([builds.performance-report](20-builds.md#builds.performance-report)).

Checked by: the costs suite, whose `PROVED overflow` and `KEPT overflow` annotations in `tests/costs/checks.lt` the toolchain's tests check (`compiler/stilt-cli/tests/costs.rs`), and the compiler's tests of the analysis (`compiler/stilt-types/src/verify/tests.rs`).
