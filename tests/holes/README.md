# Holes suite

Programs whose holes have a known context, which `stilt show` must report ([Goals](../../docs/design/goals.md), `hole-context`; [Agent syntax](../../docs/design/agent-syntax.md), "Typed holes as context"). Each hole's context is derived by reasoning from the rules below and the records they cite, never by running an implementation. A program is a `.lt` file, or a directory that holds one, as in the conformance suite, and has no error, so that `show` writes nothing on stderr.

## What a hole's context is

`stilt show` reports each hole of the part it shows, in the order Hazel measured:

1. **Expects.** The type the hole's context expects ([declarations.typed-holes](../../reference/10-declarations.md#declarations.typed-holes)), as a program writes it.
2. **Effects.** What code at the hole may perform, each element as a row writes it ([effects.rows](../../reference/12-effects.md#effects.rows)): the row of the hole's function; `io, raise<E: Show>` in a test or a doc example ([program.test-declarations](../../reference/04-programs.md#program.test-declarations) and [program.doc-examples](../../reference/04-programs.md#program.doc-examples)); nothing in a constant. A closure that a non-escaping parameter takes passes its effects through to the call ([effects.non-escaping-parameters](../../reference/12-effects.md#effects.non-escaping-parameters)), so its holes may perform what the code around the call may; one that an escaping parameter takes may perform what its type holds.
3. **Without.** The implicit effects that a `without` of the function or of its module rules out where the hole is ([facts.without](../../reference/15-facts.md#facts.without); [effects.without-panic](../../reference/12-effects.md#effects.without-panic) and [effects.without-overflow](../../reference/12-effects.md#effects.without-overflow)).
4. **Types.** The definitions of the types that the expected type and the error type the hole may raise name, in the order they name them, each once: every declared type but the prelude's, each as `stilt fmt` writes its declaration, without its doc comments.
5. **In scope.** The bindings that code at the hole can name, each with its type, in the order they are bound: the parameters, `self` first, then each binding of a pattern whose scope holds the hole. Of two bindings of one name, only the later shows, since it hides the other.
6. **Fits.** The headers of at most 10 functions whose result fits, each as code calls it, on one line: its qualifier, its name, its type parameters, its parameters, its result and its row, as in `List.take(self, n: i64) -> List<T>`. A function fits when, its type parameters made fresh and a method's receiver made one with the binding it is called on, its result can be the expected type; when each type parameter that this fixes implements the traits that bound it; when the hole may perform its row; when a `without` where the hole is doesn't rule out its implicit effects; and when its receiver, if it is `inout`, is a binding code may pass `inout`, a `var` or an `inout` parameter ([modes.kinds-of-access](../../reference/13-modes.md#modes.kinds-of-access)). A result that is one of the function's own type parameters, which the call doesn't fix, fits every hole and tells nothing, so it doesn't fit. The function the hole is in isn't listed. The candidates come in this order, each once:
   1. the functions of the hole's module, in source order;
   2. the methods of the bindings in scope whose type isn't the expected type, by binding in the order of *In scope*, each binding's inherent methods in source order, then the methods of the traits it implements: the prelude's, its module's, then its imports' ([traits.method-resolution](../../reference/11-traits.md#traits.method-resolution));
   3. the public functions of the modules the hole's module imports, in the order of their names, each written after its module's last name, as `fs.read`;
   4. the functions without a receiver of the expected type's own impls, as `List.new`;
   5. the prelude's functions;
   6. the methods of the bindings of the expected type, which only make one such value of another.

A body with an error has no context: what its holes expect isn't known ([facts.bodies-with-errors](../../reference/15-facts.md#facts.bodies-with-errors)).

## Annotations

A hole's line ends with `//~ HOLE`, and the comment lines right after it each hold one `//~ key: value` of its context:

| Key | Expects |
| --- | --- |
| `expects` | The expected type |
| `effects` | The effects, joined by `, `, or `none` |
| `without` | The implicit effects ruled out, joined by `, `; `none` if the key is absent |
| `type` | A type's definition, its whitespace runs written as single spaces; one line per type, in order, and none if the key is absent |
| `in scope` | A binding, as `name: Type`; one line per binding, in order, and none if the key is absent |
| `fits` | A header that fits; those the lines give must be listed in their order, with others between them |
| `not` | A header that must not be listed |

## What is checked

`just holes`, part of `just test` and of `just ci`, runs `stilt show --json` on each module of each program, and checks that the holes it shows are exactly those the annotations mark, each with the context they expect, and that none lists more than 10 headers.
