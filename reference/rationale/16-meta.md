# Rationale: Macros, staging and reflection

Stilt's compile-time code folds generics, derives and macros into one language with one meaning. A generic body is checked once, against its bounds, before anything instantiates it. A staging annotation marks what a release build may compute ahead of time, without adding a second body. A derive is an ordinary library function that reads a type's shape, and macros are left for what functions can't express: new syntax. Every rule of this chapter keeps that code pure and deterministic, checked where it is written, and visible to the tools that read a program without running it.

## Pattern macros

A function can't take a block to run only sometimes, or bind a name that its caller chose: those need new syntax. Pattern macros give small sugar of that kind, as Scheme's `syntax-rules` and Rust's `macro_rules!` do. A pattern macro is a list of arms, each a pattern over tokens and a template that replaces them ([macros.syntax-declarations](../16-meta.md#macros.syntax-declarations), [macros.patterns](../16-meta.md#macros.patterns), [macros.templates](../16-meta.md#macros.templates)). Nothing runs but matching and substitution, and no string is ever spliced into code.

A use is marked with `!` and its arguments are read as balanced tokens ([macros.uses](../16-meta.md#macros.uses)), so every tool parses every file without resolving names. Uses without `!`, as `unless(c) { … }`, are the alternative, and are rejected. The parser would have to know which names are macros to read their arguments, and the published grammars, which keep every prefix of a program viable, couldn't describe a file.

A pattern's fragments are forms the grammar already has. So a template is checked as code where the macro is declared ([macros.checked-templates](../16-meta.md#macros.checked-templates)), and a mistake in it is reported once, at the declaration, as a generic body's is. The follow rules of [macros.pattern-checks](../16-meta.md#macros.pattern-checks) keep an expression, a pattern or a type from reading on into what follows it. A pattern then means the same when the grammar grows, and Rust's follow sets exist for the same reason. The fragments that one repetition of a template names come from one repetition of the pattern ([macros.templates](../16-meta.md#macros.templates)), so they have one length and the template repeats them in step.

Matching takes the first arm that matches and never goes back into an arm ([macros.matching](../16-meta.md#macros.matching)). A reader can tell which arm a use takes by reading the arms in order, and matching takes time proportional to the tokens. Token-tree fragments, which match any balanced tokens, are not part of pattern macros: procedural macros read tokens, and an embedded language needs their cursor anyway.

A fragment stays one form, as if parenthesized ([macros.expansion](../16-meta.md#macros.expansion)), so `$x * 2` never regroups the expression it is given, as C's preprocessor does. A fragment named twice is evaluated twice, as written: a macro is substitution, and a template that wants one evaluation binds the fragment first.

Hygiene follows Scheme's ([macros.hygiene](../16-meta.md#macros.hygiene)). Names that the template binds are fresh, names that it writes resolve where the macro is declared, and names that the user passes resolve where the use is. An expansion then means what its author wrote wherever it is used. Unhygienic templates, and a way to break hygiene, are rejected: a template that captures the user's names means something different in every module that uses it. A name that the user should see is passed in as a fragment, as `swap!(a, b)` passes both names.

Macros that declare items are rejected. An item that a macro makes is an API that no source declares, which `stilt show` and the checks of a package's API would have to expand to see. Declaring a macro puts a module in the advanced tier, while using one doesn't ([macros.advanced-tier](../16-meta.md#macros.advanced-tier)). A library may offer `unless` or a literal for its own collection. A core module that uses it stays readable as core code, as calling a method of an advanced trait leaves a module in its tier.

## Staging annotations

A function with a value parameter, as `dot<n: i64>`, runs one body for every `n` in a debug build. A release build can unroll its loop over `0..n` and keep one branch of a test on `n`, but only if the program says which parts are known at compile time. A staging annotation says so ([meta.staging-annotations](../16-meta.md#meta.staging-annotations)). It is an assertion that the compiler checks ([meta.static-expressions](../16-meta.md#meta.static-expressions), [meta.not-static](../16-meta.md#meta.not-static)), as `without` is. A reader sees where a release build unrolls, and a `comptime for` over a `List` parameter is an error, where it would otherwise be a silent loop at run time.

The annotation's meaning is the program without it ([meta.erasure](../16-meta.md#meta.erasure)). Every static expression is code that the program without annotations runs too. That program is then the meaning, with no proof falling on the user, and the conformance runner checks it on every test that writes `comptime`. Tan and Wei show when a staged program equals its erased version, once inserting code is typed as an effect. Stilt's static expressions are those whose row is empty, which is that typing. Four alternatives are rejected:

- **Specialization hints** that ask a release build to specialize a call or a function. A release build specializes every instantiation that a program reaches, so a hint would ask for nothing, and it would be a declaration that changes nothing a program does.
- **Compile errors for panics in static code,** as Zig gives. A debug build compiles one body for every value of a value parameter, so it can't know that `n / 0` panics for every caller. A program that failed only in release builds would break the rule that the program without annotations is the meaning.
- **A second body for compile time,** as `if comptime { … } else { … }` would give. One body per function keeps a function's meaning independent of how it is built.
- **Inferring static loops without an annotation.** The annotation tells a reader where a build unrolls, and is checked, as a limit is.

Lazy, duck-typed compile-time code, as in Zig, where a body is checked only when something instantiates it, is the larger alternative to this whole design. It is rejected: unused code would hold errors nobody sees, errors would appear at each instantiation, and a language server couldn't report errors in generic code.

The variables of a `comptime for` are values, never type arguments ([meta.staged-loops](../16-meta.md#meta.staged-loops)). A type that depends on a loop variable would be a type that depends on a value. Value parameters keep such types out by taking only literals, constants and parameters as arguments.

## Shapes

A derive should be a library function that reads its type. One function then serves every record and variant type, no type gains an API from compile-time code, and nothing is generated per type. Reflection gives such a function its type's **shape**, an ordinary value of the module `std.meta` ([meta.std-meta](../16-meta.md#meta.std-meta), [meta.shape-and-name](../16-meta.md#meta.shape-and-name)). Reflection as members of every type, as `T.fields()` without an import, is rejected. A type's own `fields` or `shape` would become an error, and existing programs declare such names. So `T.shape()` exists only where `std.meta` is imported, and a type's own member of that name is found first.

Each case of a shape gives accessors, and none refines `T` ([meta.shapes](../16-meta.md#meta.shapes), [meta.shape-accessors](../16-meta.md#meta.shape-accessors)). An integer is read through `n.text(value)` and a float through `get`. Every arm's types are those its pattern gives, and the checker narrows no type inside a branch, which Stilt does nowhere else. Arms that refine `T`, as an `Int` arm in which `T` is `i64`, are rejected for that reason, and because each integer type would need an arm of its own. A set and a map appear as lists, in insertion order, so a derive writes and reads them with the code it uses for lists. Their `make` settles equal elements and keys as `Set.from_list` and `Map.from_entries` do.

A shape shows private fields ([meta.private-fields](../16-meta.md#meta.private-fields)). A type's fields have its visibility, and the code that called the reflecting function chose to hand over the value. A derive that skipped private fields could neither write nor read back a value of a type with one.

## Fresh types, fields and cases

`f.get(value)` has a type that depends on `f`, which looks like dependent typing. None is needed: the type of a field, an element or a payload is a fresh type of the arm or the loop that reads it ([meta.fresh-types](../16-meta.md#meta.fresh-types)). A fresh type works as an existential type does: code there passes it on to a generic function, but can't name it. A generic body is still checked once, before anything instantiates it. A value of a fresh type can't leave its arm ([meta.leaving-arm](../16-meta.md#meta.leaving-arm)), since outside the arm nothing could say what its type is. Its own code, E0351, says so, where a plain mismatch would only say that two types differ.

`fields.build` makes a value from one call per field ([meta.building](../16-meta.md#meta.building)). Its callback is polymorphic in the field's type, so one closure can give every field a value. It stops at the first raise, so a reader that fails on one field reads no further.

## What reflects

A function that reflects on its type parameter needs no bound ([meta.reflects](../16-meta.md#meta.reflects)). A bound written for reflection, as `T: Reflect`, is the alternative, and is rejected. Every generic function over the user's types would carry it, and its callers' bounds would grow with it. The fact is inferred instead, as implicit effects are, and shown by `stilt show`. Since no `without` names it, it is no part of a package's API.

Some types have no shape, as a function type or a `View` ([meta.types-without-shape](../16-meta.md#meta.types-without-shape)). Panicking at run time on such a type is rejected. The call that gives the type is known while the program is checked, so the error is reported there, with the chain of functions that reflect. A generic caller that passes its own type parameter on reflects in turn, so the error lands where a type without a shape is first written ([meta.unseen-instantiations](../16-meta.md#meta.unseen-instantiations)). The guards let a derive use a type's own impl where it has one, so a type that holds a function but implements `ToJson` is still written as JSON.

**How reflection is compiled.** None of this is part of the language. A debug build passes a descriptor of `T`, beside its witness, to a function that names `T.shape()`, `T.name()` or a bound test on `T`, or gives `T` to one that does. The descriptor holds the type's name, its shape and the descriptors of its parts, which a recursive type makes cyclic. Such a function is compiled once and serves every type, holding `T`'s values in one word. A bound test looks the impl up in the descriptor's table of the type's impls.

The structural impl of a tuple, a record, a variant type or an array is code that every type of its shape shares. It walks a value's parts through the descriptor and calls the parts' impls in the order the compiled impl calls them, so it gives the same results, hashes and text included. An edit of a type changes its descriptor and compiles no reflecting function again. In prototypes, such code takes 1.5 to 1.7 times the time of code written by hand, and release builds specialize it per type, which closes the gap. Compiling every reflecting function per type in debug builds is the alternative, and is rejected: an edit of a type would compile again every function that reflects on it.

## Bound tests

`if T: Show { … }` lets one body take a faster or richer path for types with an impl ([meta.bound-tests](../16-meta.md#meta.bound-tests)), without a second function and with the meaning of one body. Inside the branch `T` has the bound, so its methods resolve. Negative bound tests, in which the `else` branch knows that `T` has no impl, are rejected. An impl added in another module would change what an `else` branch was checked against. A bound test is static ([meta.static-reflection](../16-meta.md#meta.static-reflection)), so `comptime if T: Show` lets a release build keep one branch, while the same test without `comptime` runs and gives the same answer.

## Procedural macros

What a pattern macro can't express, an embedded language checked against a file, or a notation compiled to code, needs code that runs while the program is checked. A procedural macro is that code: a compile-time function from syntax to syntax ([macros.procedural-declarations](../16-meta.md#macros.procedural-declarations)). Its design draws on Rust's `syn`, Racket's `syntax-parse`, Scala 3, Lean 4 and Elixir, and on Stilt's own forms:

- tokens are data, read by a cursor written in Stilt ([macros.cursor](../16-meta.md#macros.cursor));
- code is opaque and only spliced ([macros.tokens-and-code](../16-meta.md#macros.tokens-and-code));
- errors carry spans that only the input can give ([macros.raised-errors](../16-meta.md#macros.raised-errors));
- every quote is resolved where it is written, so hygiene stays lexical ([macros.quote-hygiene](../16-meta.md#macros.quote-hygiene)).

A macro's parameters are typed by what a use gives them. Its result is an expression, a pattern or a type, never an item, so no type gains an API that no source declares. Macros that declare items, as Rust's derive macros, are rejected for that reason, and a derive is a function that reflects.

A macro performs nothing ([macros.procedural-bodies](../16-meta.md#macros.procedural-bodies)). A file it reads is named at the use and read by the compiler ([macros.named-files](../16-meta.md#macros.named-files)). So the same use always expands to the same code ([macros.running](../16-meta.md#macros.running)), and a build reads the same files on every machine. An edit of a named file expands the uses that name it again. A macro's body is not compared with other bodies for duplicates, since no call can stand in for it in its own module.

A macro's run is limited to a fixed number of steps ([macros.step-limits](../16-meta.md#macros.step-limits)), which neither code nor a manifest changes, unlike Zig's branch quota. A macro that can't finish then fails at once, at the same use in every implementation. Every value the run holds counts toward its memory, whatever its kind, so a dependency's macro can hold no more in records and variants than in lists.

The expansions of a use hold at most 100,000 tokens ([macros.expansion-size](../16-meta.md#macros.expansion-size)) for the same reason. Nesting is bounded at 128, but a macro that uses another twice at each of many levels doubles its code at each. Such a macro would make every program that uses it run the compiler out of memory. Counting every expansion that the use leads to, nested ones included, makes the bound the same however the macros split their work. A use ends at its first error, and the expansions that would still pass are not reported, so a use that fails costs no more than its bound.

Its macros are imported with `meta use` ([macros.meta-use](../16-meta.md#macros.meta-use)), and only what their expansions name joins the program ([macros.linking](../16-meta.md#macros.linking)). A macro module's parsers and helpers stay in the compiler. Several alternatives are rejected:

- **Macros that inspect code,** matching a `meta.Expr` as a tree. Both implementations would have to agree on every shape of a tree, every change of the grammar would break macros, and Scala 3's reflection API shows the size such an interface reaches. A macro that needs structure reads tokens.
- **Token patterns with procedural bodies,** as Racket's `syntax-parse`. The cursor expresses recursive grammars, which patterns alone don't.
- **Quotes whose form comes from their expected type.** A tool would need types to parse a file. The form is written instead, as `quote type { … }` ([macros.quote](../16-meta.md#macros.quote)).
- **Quotes resolved in the expansion,** so that one quote sees another's bindings by name. A quote's meaning would depend on where its code lands, and `meta.fresh` names a binding that several quotes share.
- **Names made from any string,** as Rust's `Ident::new`, and **a way to break hygiene,** as Julia's `esc` or Rust's `Span::call_site`. A macro could bind a name that the user sees without the user writing it, which is how hygiene breaks. Names come from the user's tokens or are fresh, and a name the user should see is passed in as a part.
- **Running macros as separate programs,** as Rust's procedural macro crates. A build would run arbitrary code with the user's permissions, and the editor couldn't run it cheaply.

A splice writes a value of a primitive type as a literal ([macros.literal-splices](../16-meta.md#macros.literal-splices)). The literal is escaped so that a string never interpolates, and typed where it lands, so a macro that computes a number writes it as a user would. A function that writes quotes is an ordinary function ([macros.outside-run](../16-meta.md#macros.outside-run)), which a program may also call. There it makes code that nothing can observe, so a macro's helpers can be tested without a second kind of function.

**How macros run.** None of this is part of the language. The compiler runs a macro from a bytecode of its module. It caches each use's expansion by three keys: the code of the macro's module and its imports, the parts' tokens with spans relative to the use, and the paths and contents of the files they name. Moving a use runs nothing again.

## Expansions

Errors point at the user's tokens ([macros.errors-in-expansions](../16-meta.md#macros.errors-in-expansions), [macros.failed-uses](../16-meta.md#macros.failed-uses)). A mistake in a fragment or a part is the user's, and is reported where the user wrote it. A mistake in a template's own tokens is the macro's, and is reported at the use with the template's line, since the user can't edit the template. A failed use reports nothing further, so one mistake gives one diagnostic.

Expanded code is the using function's ([macros.expansion-effects](../16-meta.md#macros.expansion-effects)). Its effects are inferred there and its `without` limits them, so a macro can't hide an effect. The capabilities that an expansion's own tokens name are the declaring package's, as a call into the package would be. So a dependency can't reach the file system through a macro when its grant doesn't allow it.

`stilt show` prints a use as written, and its expansion with `--expanded` ([macros.showing](../16-meta.md#macros.showing)). Showing expansions by default is rejected: the user wrote the use, edits address it, and the expansion is one flag away. Fresh names are printed with a `#` and a number, which no program can write, so a printed expansion never reads as code that captures a name. `stilt fmt` leaves the tokens of a use's groups as written, but for their indentation ([macros.formatting](../16-meta.md#macros.formatting)), since it resolves no macro and can't know what form the tokens take.
