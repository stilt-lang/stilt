# 10. Declarations: rationale

Two choices run through the forms of a module's items. Every name has exactly one home, which rules out type aliases and overloading. The core tier stays simple to infer and to explain, so structural records belong to the advanced tier.

## Record types

Records are nominal ([declarations.records](../10-declarations.md#declarations.records)): a function that takes a `Point` takes nothing else, even a record with the same fields. TypeScript, Elm and PureScript let a function take any record with a field `name`, and let a record type be written inline. Those row-polymorphic and anonymous records make inference and its error messages harder, in the tier that is meant to stay simple. So they belong to the advanced tier ([records.anonymous-types](../07-types.md#records.anonymous-types), [records.record-bounds](../07-types.md#records.record-bounds)), where a module that uses them says so through its tier.

## Variant types

Payloads are positional ([declarations.variant-types](../10-declarations.md#declarations.variant-types)). The name of a payload field documents it, as in `Circle(radius: f64)`, but appears in no pattern and no constructor. Named fields in patterns would give each variant two forms of pattern, as Swift's labelled associated values do. A variant with a payload is a function ([declarations.constructors](../10-declarations.md#declarations.constructors)), so `[0.5, 2.0].map(Circle)` needs no closure.

Recursive types need no box ([declarations.recursive-types](../10-declarations.md#declarations.recursive-types)), where Rust needs a `Box<T>` in each. Every value has value semantics, so an implementation boxes a recursive type itself. Only a record that contains itself through fields and tuples alone is rejected, because no value of it could ever be built. A variant type, a collection or a function type between gives the chain a way to end, as `None` and `[]` do.

## No aliases

Type aliases are rejected ([declarations.no-aliases](../10-declarations.md#declarations.no-aliases)). An alias gives one type two names, which breaks the rule that every name has one home. It also makes error messages harder to read, because a message can name the type either way, as Haskell's and TypeScript's messages do. A single variant, `type UserId = | UserId(i64)`, gives a real nominal type instead, which the checker keeps apart from `i64`. The single variant needs its `|` because without it the declaration reads as an alias.

## Type parameters and arguments

A type's parameters take no bounds ([declarations.type-parameters](../10-declarations.md#declarations.type-parameters)). Bounds are written where code needs them, on functions and impls ([traits.bounds](../11-traits.md#traits.bounds)). So a generic record can hold a map, as `type Cache<K, V> = { entries: Map<K, V> }` does, and the functions that find its keys say that they need `K: Eq + Hash`. Haskell dropped datatype contexts for the same reason: a bound on the type has to be repeated on every function that uses it.

A type written in a signature or an annotation always has all its arguments ([declarations.type-arguments](../10-declarations.md#declarations.type-arguments)). So a reader sees `List<i64>` where an item's interface is stated, while an expression names the type bare and inference fills the arguments in ([types.no-type-arguments](../07-types.md#types.no-type-arguments)). An empty list of generics is rejected ([declarations.generic-lists](../10-declarations.md#declarations.generic-lists)), because `fn f<>()` says nothing that `fn f()` doesn't.

## Namespaces and names

A module has two namespaces ([declarations.namespaces](../10-declarations.md#declarations.namespaces)), so a variant may share its type's name. That is the newtype idiom of `type UserId = | UserId(i64)`. In `Name.member`, `Name` is looked up as a type first ([declarations.name-lookup](../10-declarations.md#declarations.name-lookup)), so `UserId.new(…)` reaches the associated function of the type even though the variant has the same name.

Expressions name the variants of another module with their module ([declarations.qualified-variants](../10-declarations.md#declarations.qualified-variants)). Each variant then has one name wherever it is built, and a search for `shapes.Circle` finds every place that makes one. A pattern names them through the matched type instead ([patterns.variants-by-type](../09-patterns.md#patterns.variants-by-type)), where the module would only be repeated.

## Built-in types

`Never` has no values and converts to any type ([declarations.never](../10-declarations.md#declarations.never)), as Rust's `!` and TypeScript's `never` do. So `exit`, `raise` and `return` stand wherever a value is expected. Let-else and the `else` fallback rely on it ([patterns.let-else](../09-patterns.md#patterns.let-else), [expressions.option-fallback](../08-expressions.md#expressions.option-fallback)).

## Function types

A row after a function type belongs to the innermost function type without one ([declarations.function-type-rows](../10-declarations.md#declarations.function-type-rows)). So a function that returns a function with effects is written as it reads, and parentheses give the row to the outer function when that is meant. A parameter's mode is part of a function type ([declarations.function-types](../10-declarations.md#declarations.function-types)), because a caller of a function value must know which arguments it marks `inout`.

## Functions

A function's signature is written in full ([declarations.function-declarations](../10-declarations.md#declarations.function-declarations)), and types are inferred only inside bodies ([types.inferred-per-body](../07-types.md#types.inferred-per-body)). Editing a body then never changes the types of a caller, and a reader learns what a function takes and returns from its signature alone. Haskell and OCaml infer signatures too, and a change in one body there can change the type of a function far away.

A parameter is a name with its type and mode, and nothing more ([declarations.parameters](../10-declarations.md#declarations.parameters)). Arguments are positional, with no defaults, as [expressions.arguments](../08-expressions.md#expressions.arguments) says of every call. Python's and Kotlin's defaults would give one function several call forms.

A `without` clause isn't part of the signature ([declarations.limits](../10-declarations.md#declarations.limits)). It states what the compiler checks about the body, not what a caller passes or gets. So an impl's function may promise more than the trait's declaration asks.

## Typed holes

A hole stands for code not yet written and takes the type its context expects ([declarations.typed-holes](../10-declarations.md#declarations.typed-holes)), as holes do in Agda, Idris and Haskell. A program can then be checked, and its finished parts run, before every part is written ([declarations.running-holes](../10-declarations.md#declarations.running-holes)). Each hole is a warning, so none is forgotten, and a release build, which is what ships, refuses them.

In the standard library's sources, the same `?` marks the native items that each implementation provides ([declarations.native-items](../10-declarations.md#declarations.native-items)). Every signature of the library is then written in Stilt.

## Constants

A constant's value is a constant expression ([declarations.constant-expressions](../10-declarations.md#declarations.constant-expressions)), built from literals, structures and other constants. It is computed at its first use ([declarations.constant-evaluation](../10-declarations.md#declarations.constant-evaluation)). The one way it can fail, a unary `-` that overflows, then fails where the program first needs it, and a constant that the program never uses never fails.

A constant's type is written, as a function's signature is, so a body that uses it never depends on the inference of its value.
