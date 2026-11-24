# 7. Types and generics: rationale

## Inference

Types are inferred within each body, from the signatures of the items it uses ([types.inferred-per-body](../07-types.md#types.inferred-per-body)). Every function writes its signature in full, so a body's types never depend on another body. Changing one function's body never changes the types of another, and an error is reported in the body that holds it.

Inference goes through a body in evaluation order, and checks each expression against its expected type ([types.expected-types](../07-types.md#types.expected-types)). So a mismatch is reported at the expression that differs, in the branch or element that disagrees with the first one.

Some positions need their type before anything after them can help ([types.known-types](../07-types.md#types.known-types)). A method call is resolved by its receiver's type, never by its arguments ([traits.no-overloading](../11-traits.md#traits.no-overloading)), and the same holds for a field, an index and the iterable of a `for`. Only the outermost constructor is needed, so `var xs = []` followed by `xs.push(1)` is valid. Nothing is resolved through the bounds of a range, so they aren't among these positions ([types.range-bounds](../07-types.md#types.range-bounds)), and a loop variable can take its type from its use.

A type that the body leaves undecided is reported only when the body has no other error ([types.undecided-types](../07-types.md#types.undecided-types)), because another mistake is often what left it undecided. It is reported at the expression that introduced it, once for each such expression ([types.undecided-type-location](../07-types.md#types.undecided-type-location)). Two implementations then agree on where and how often, and the annotation that fixes it goes there.

Expressions take no type arguments ([types.no-type-arguments](../07-types.md#types.no-type-arguments)), so `<` in an expression is always less-than, and a parser never has to guess. The alternative is Rust's turbofish, `f::<T>()`. Its syntax is clumsy, and an annotation gives inference what it needs.

A closure bound by `let` gets one type and is never generalized ([types.closures-not-generalized](../07-types.md#types.closures-not-generalized)). The alternative is the generalization of `let` in ML. Stilt generalizes only declared functions, whose signatures say so. A `let` that silently became generic would make a body's types depend on how a closure is used further on in it.

## Fields

A field access needs a record or a tuple that has the field ([types.field-access](../07-types.md#types.field-access)). Calling a field that holds a function is a method call. A value carries behaviour as a record of functions, and that record is used as `r.m(x)`.

## Fields through an `Option`

Programs often read through data that is partly filled in, such as the city of an order's customer's address, where the customer or the address may be missing. A field access on an `Option` reads through it, with no mark ([types.fields-through-option](../07-types.md#types.fields-through-option)). The type already says that the value is optional. A reader who misses that is told where the value is used. A path through an `Option` used where the type inside is expected is a type mismatch, whose message suggests `else`.

The read adds no level of `Option` ([types.option-field-types](../07-types.md#types.option-field-types)), so a path holds one `Option` however many of its links are optional. Swift, Kotlin, C# and TypeScript give optional chaining the same flat type. Whether a level is added depends on the field's type as the access itself sees it ([types.option-field-known](../07-types.md#types.option-field-known)), so a generic body has one meaning for every instantiation.

The alternatives, and why each loses:

- **Optional chaining with `?.`,** as in Swift, Kotlin and C#. It makes `?.` a second way to reach a member, with rules of its own that a reader has to know. These include how far a `?.` reaches and that parentheses end its reach. A rest of type `Option<U>` isn't wrapped again, and one of type `()` makes the chain `()`. They also include a key-path form that starts with `?.`, and a hole before a dot written `(?)`. And the mark repeats what the type says. Python's PEP 505, which proposes the operator, has stayed undecided since 2015. Its critics found it unreadable, and its authors dropped the `?()` call form, because the need is to read through partly filled data. Go refused new syntax for error handling in 2025, and Gleam refused a `?` operator, each to keep one way to write a thing. With no `?.`, a `?` before a dot is a hole ([types.hole-before-dot](../07-types.md#types.hole-before-dot)).
- **`e?`, reading through an `Option` up to a boundary,** such as the left operand of `else`. It still marks each link, and adds a rule for where the boundary is.
- **Reading through an `Option` with methods too.** The methods of `Option` would clash with those of the value inside. `order.customer.tags.filter(f)` would have two meanings, which one applied would depend on whether `Option` has a `filter`, and adding a method to `Option` would change programs. A method may also perform `io` or raise, and skipping it on `None` would hide a branch around an effect, while a field read has no effects. So only fields read through ([types.only-fields](../07-types.md#types.only-fields)). A method at the end of an optional path is called through `map`, as `order.customer.name.map(.len())`, or after a fallback. On a path that ends in a list, `map` and `filter` are those of `Option`, as `Optional.map` is on an optional array in Swift and Rust.
- **Patterns that reach through fields,** as the property patterns of C#, `order is { Customer.Address.City: var c }`, which read through `null` with no mark. A read with a default would still need a `match` or a let-else.
- **Flow typing,** as in Kotlin, TypeScript and Dart, where a test on `o.customer` gives it the type `Customer` until the end of the branch. The same expression would have different types on different lines.
- **A `do` block, or the `use` of Gleam.** Both turn the rest of a block into a closure, which `return` and `break` can't cross.

A field read through an `Option` is a copy, and is no place ([types.option-field-not-place](../07-types.md#types.option-field-not-place)): assigning to it would change a value that nothing keeps. Key paths read through an `Option` as any field does ([types.option-key-paths](../07-types.md#types.option-key-paths)), so `orders.filter_map(.customer.address.city)` needs no symbol either. With `Option.map`, `Option.filter` and `List.filter_map`, key paths cover what `and_then` and a filtering symbol do in other languages. A filter takes a predicate, and no symbol writes `age.filter(.is_adult())` more briefly.

## Polymorphic function types

A generic function is instantiated where it is named, so `quoted<T: Show>` passed as an argument becomes `quoted` at one type. With a plain function type, a function that shows an integer and a string through the same argument can't be written. Rank-2 types, as in the `RankNTypes` of GHC, let the argument stay generic, and each call inside the function instantiates it afresh ([polymorphism.instantiation](../07-types.md#polymorphism.instantiation)). A value with behaviour is a record of functions, so a field may need a generic function as well ([polymorphism.placement](../07-types.md#polymorphism.placement)).

What may be given for one ([polymorphism.rigid-types](../07-types.md#polymorphism.rigid-types), [polymorphism.arguments](../07-types.md#polymorphism.arguments)) is checked as a generic function's body is, with each type parameter a type about which only its bounds are known. A function fixed to one type can't stand for every type: no type argument makes its type equal to the polymorphic one, so it is a mismatch.

The alternatives, and why each loses:

- **Polymorphic types everywhere,** as the impredicative types of GHC, `List<fn<T>(T) -> T>` included. Inferring a type argument that is itself polymorphic is undecidable in general, and its errors are hard to explain. Parameters and fields cover what a value with behaviour needs.
- **Polymorphic locals,** as `let f: fn<T>(T) -> T = id`. A generic function is already a polymorphic value wherever it is named, so a local adds nothing that a name doesn't.
- **Row variables in polymorphic function types,** as `fn<T, e>(T) / e`. A parameter that isn't `escaping` already passes its argument's effects through, and an `escaping` one names its row ([polymorphism.effects-and-escaping](../07-types.md#polymorphism.effects-and-escaping)).

A value of a polymorphic function type carries no dictionaries of its own. Each call passes the dictionaries of the bounds at its instantiation, as a call of a generic function does ([the rationale of traits](11-traits.md#elaboration)). So a strategy that shows, compares or hashes any value it is given is one field of a record.

## Polymorphic recursion

A generic function calling itself at another type needs nothing new ([polymorphism.recursion](../07-types.md#polymorphism.recursion)), as when a traversal of `Nested<T>` calls itself at `Nested<List<T>>`. Every function's signature is written, so the call is checked against it. Such a function reaches types without bound, so an implementation can't compile a copy for each one. It passes the dictionaries and layouts at run time, and the release build's performance report lists each such group ([builds.performance-report](../20-builds.md#builds.performance-report)).

## Lazy values

Evaluation is strict, and laziness is opt-in through `Lazy<T>`, a value computed on its first use and kept ([polymorphism.lazy-values](../07-types.md#polymorphism.lazy-values)). The alternative, lazy evaluation by default as in Haskell, makes performance hard to predict. `Lazy` is in the module `std.lazy`, outside the prelude, whose names every program reserves.

The function of a `Lazy` performs no effect and waits for nothing ([polymorphism.lazy-waits-for-nothing](../07-types.md#polymorphism.lazy-waits-for-nothing)). So nothing a program does can tell when it runs, and every copy shares one result ([polymorphism.lazy-unobservable](../07-types.md#polymorphism.lazy-unobservable)). The alternatives, and why each loses:

- **A `Lazy<T>` whose function may perform effects.** When the effect happens would depend on which code first asks for the value, and two copies could be told apart.
- **`is_forced`, or `Show` and `Eq` on `Lazy`.** Each would let a program observe when the value is computed, or compute it unseen behind an operator or an interpolation.

A `when` in the function could wait for the code that asked for the value, or reach the `Lazy` itself through a shared value. So the checks reject the `when`s they see, and the run panics with `deadlock` at one they can't see, before it holds anything. A table built on first use is then a field of type `Lazy<…>`, computed once, whichever copy asks.

## Anonymous records

A core record is nominal: two records with the same fields are different types, and a function that reads a `name` takes one declared type. The advanced tier adds two structural forms: a record type written where it is used ([records.anonymous-types](../07-types.md#records.anonymous-types)), and a function that takes every record with the fields it names ([records.record-bounds](../07-types.md#records.record-bounds)).

An anonymous record's fields compare, hash and show in alphabetical order ([records.field-order](../07-types.md#records.field-order)). Two literals of one type may write their fields in different orders, so the written order isn't part of the type and can't be the order. An implementation lays an anonymous record out with its fields in alphabetical order too.

The alternatives, and why each loses:

- **Converting a literal to the declared record expected,** as `let p: Person = { name: "Ada", age: 36 }`. Two records with the same fields are different types, and a conversion that depended on the expected type would make them the same in some places ([records.anonymous-literals](../07-types.md#records.anonymous-literals)).
- **Showing fields in written order.** Two literals of one type may write them in different orders.
- **Aliases for anonymous types.** `type` declares a nominal type in every tier ([records.no-home](../07-types.md#records.no-home)), and a long anonymous type is a sign that it wants a name.

## Record bounds

Stilt has a form for "any type that has what I need": a bound. A record bound makes the fields a record needs a bound, `P: { age: i64, .. }` ([records.record-bounds](../07-types.md#records.record-bounds)). An open parameter type, `{ name: str, .. }`, is that bound on a hidden type parameter ([records.open-parameter-types](../07-types.md#records.open-parameter-types)), as `impl Trait` is in an argument in Rust. So the type that comes back is the caller's own, and nothing is inferred beyond what a type parameter already is. A record bound passes the offsets of its fields in the record's layout, as a trait bound passes a dictionary.

A record bound's `..` is required ([records.bound-fields](../07-types.md#records.bound-fields)), because a bound that named every field would be a type. The diagnostic's fix adds it, and the bound is read as if it had it, so the one mistake causes no other.

The alternatives, and why each loses:

- **Row variables,** as `fn renamed<r>(p: { name: str | r })` in the style of PureScript and Elm. A bounded type parameter already says that the type that comes back is the caller's, and keeps a `Person` a `Person`. It needs no new kind of variable and no row to infer.
- **Open types as results and fields,** an existential record. The type that an open record type stands for must come from the caller. A function that returns some record writes an anonymous type.

## Update

Update syntax ([records.update](../07-types.md#records.update)) changes some fields of a record and keeps its type. So a declared record is copied with some fields changed, `Person { ..p, age: 37 }`, without listing the others. And `renamed<P: { name: str, .. }>(p: P, to: str) -> P` gives back a `Person` when it is given one. The alternative is an update that adds or removes fields, as `{ ..p, email: e }` with a new field. It would compute the result's type from rows, which makes inference and its errors hard, and is why core keeps rows out of records ([records.update-fields](../07-types.md#records.update-fields)).

## Variadic generics

A tuple's arity is part of its type. So a function over pairs, one over triples and one over quadruples are three functions, and a `zip` over two lists can't take three. A pack ([variadics.packs](../07-types.md#variadics.packs)) stands for a sequence of types. As in the parameter packs of Swift (SE-0393), a body has no way to take a pack apart, only to map over it ([variadics.spread-expressions](../07-types.md#variadics.spread-expressions)). It is spelled with the `..` of a record's update: `..` spreads a row, the fields of a record there and the elements of a tuple here. So a function over tuples of every arity is written once, as are `zip`, `apply`, adapters in the style of `curry`, and the tuple impls a library declares. A core module that calls one sees only its signature's instances and meets no new error.

The alternatives, and why each loses:

- **Variadic functions,** as `zip(a, b, c)`. Arguments stay fixed in number, so a call's arity always matches a signature's, and a tuple passes any number of values of any types ([expressions.arguments](../08-expressions.md#expressions.arguments)).
- **Taking a pack apart** by a head and a tail, as the recursive templates of C++ and type-level lists do. It makes a type-level program of every variadic function and of its errors. Mapping over a pack is what `zip`, `apply` and the structural traits need.
- **Indexing a pack tuple,** as `xs.0`. The arity isn't known, so the index could be out of range for some instantiations ([variadics.pack-tuples](../07-types.md#variadics.pack-tuples)).
- **Several packs in a type's parameters.** The arguments couldn't say where one pack ends.
- **Packs in trait parameters and polymorphic function types.** Neither is needed for tuples and functions over them, and both multiply the cases of coherence and of rigid types.

An implementation compiles a generic function once for each arity of its packs that a call reaches. A pack can grow through polymorphic recursion, as when `f<..Ts>` calls `f` at `(..Ts, i64)`. Its arity then has no bound, so the length and the elements' layouts and dictionaries are passed at run time, and the release build's performance report lists the function.

## Value parameters

A generic is checked once against its bounds, before anything instantiates it. So an error in a generic body is reported at its definition, whether or not anything uses it. Value parameters ([generics.value-parameters](../07-types.md#generics.value-parameters)) bring numbers into that one mechanism. A type may take a number as it takes a type, as a modular integer takes its modulus or an array its length. A function over such types is written once and checked once. So vectors, matrices, fixed buffers and modular integers carry their sizes and moduli in their types, and a mismatch is reported where the types meet.

A value argument is a literal, a constant or a parameter, never arithmetic ([generics.value-arguments](../07-types.md#generics.value-arguments)), and nothing is written at a call ([generics.value-parameter-inference](../07-types.md#generics.value-parameter-inference)). A call gives a value parameter its value only through the types of the arguments and the result. So a function's value parameter must appear in one of those types ([generics.value-parameters-determined](../07-types.md#generics.value-parameters-determined)). A type's value parameter needn't appear in a field, because a type is always written with its arguments. A value parameter is passed at run time as a hidden argument, beside the dictionaries of generic code. So a debug build runs one `add` for every modulus, and a release build specializes each function for the value arguments a program gives it ([builds.specialization](../20-builds.md#builds.specialization)).

The alternatives, and why each loses:

- **Value parameters of any type with equality,** such as `str` or a record. Two types with the same arguments must be one type, so arguments must compare exactly. A float's equality isn't exact, and a string or a record as an argument would make every type's equality run code while the program is checked.
- **Arithmetic in value arguments,** as `Array<T, n + 1>`. Equal types would need their arguments normalized and equations between them solved, which kept the `generic_const_exprs` feature of Rust unstable for years.
- **Value arguments written at a call,** as `fill::<3>(0)`. Expressions take no type arguments ([types.no-type-arguments](../07-types.md#types.no-type-arguments)), and an annotation gives the expected type.
- **Uppercase value parameters,** as `const N: usize` in Rust. An identifier's case says what it names, and a value parameter is a value.
- **Locals that hide a value parameter.** After `let n = 5`, `Array<i64, n>` would still mean the parameter, because types never see locals. The name would mean two things on one line ([generics.value-parameters-in-body](../07-types.md#generics.value-parameters-in-body)).

## Arrays

A fixed size is what lets an array live inline, in a local, a field or a list ([generics.array-effects](../07-types.md#generics.array-effects)), which a `List` can't. Arrays in the heap would lose the reason to have them. `Array` is in `std.array`, outside the prelude ([generics.arrays](../07-types.md#generics.arrays)), because every prelude name is reserved against user code, and a program may declare an `Array` of its own.

An array literal's length and a pattern's length are compared with the size while the program is checked ([generics.array-literals](../07-types.md#generics.array-literals), [generics.array-patterns](../07-types.md#generics.array-patterns)). A spread in a literal has no length known there. A rest that binds a name, as in `[x, ..rest]`, would have the type of an array whose size is arithmetic, which value arguments never are. So both are errors.

An array's witness gives its size from its length, as a record's gives its fields. Staging annotations read value parameters while a program is built, as in `comptime for i in 0..n` ([meta.staging-annotations](../16-meta.md#meta.staging-annotations)).
