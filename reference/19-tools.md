# 19. Properties, edits, the REPL and engines

This chapter gives what the toolchain promises of four tools:

- properties, the doc lines whose cases `stilt test` generates and shrinks the same way in every implementation;
- path-and-hash edits, which address a declaration or its body, and are refused when the code at that address has changed since its author read it;
- the REPL, which evaluates inputs in a module's scope and keeps its bindings across edits of the program's files;
- engines, the processes that hold a program's checks between commands.

Tests and doc examples are declared as [Programs](04-programs.md) says ([program.test-declarations](04-programs.md#program.test-declarations), [program.doc-examples](04-programs.md#program.doc-examples)), and run as [program.running-tests](04-programs.md#program.running-tests) says. [Syntax](03-syntax.md) gives the canonical format that hashes cover, and the grammar of what an edit replaces.

## Properties

<a id="tests.prop-lines"></a>
A doc line whose text, after `///` and any spaces, starts with `prop:` is a **property** ([syntax.doc-examples](03-syntax.md#syntax.doc-examples)). The property's text is the doc line's text after `prop:`, without the spaces that begin it. It is lexed and parsed as an example's is ([program.doc-examples](04-programs.md#program.doc-examples)). A property that doesn't parse as an expression is E0100, *syntax error*, and an annotation ends its text ([syntax.doc-comment-text](03-syntax.md#syntax.doc-comment-text)). In the tree form, a property's line is `(prop EXPR)`, as an example's is `(ex EXPR)` ([syntax.tree-form](03-syntax.md#syntax.tree-form)).

Tests: [lexical/doc_example_malformed_spec.lt](../conformance/lexical/doc_example_malformed_spec.lt), [lexical/doc_property_malformed_spec.lt](../conformance/lexical/doc_property_malformed_spec.lt), [properties/declared.lt](../conformance/properties/declared.lt), [properties/holds.lt](../conformance/properties/holds.lt), [properties/syntax_error.lt](../conformance/properties/syntax_error.lt).

Checked by: also `just parse`, which compares the trees that the compiler's parser and the reference interpreter's print, properties among them.

<a id="tests.property-form"></a>
A property must be a closure literal ([expressions.closures](08-expressions.md#expressions.closures)) with at least one parameter. Each parameter is a pattern that a closure's parameter may be, with its type written, as `|xs: List<i64>| …` or `|(a, b): (i64, str)| …`. Any other expression, and a closure with no parameter, is E0332, *property that isn't a closure with typed parameters*, at the expression. A parameter without a type is E0332 at the parameter. So is a parameter marked `inout`, which takes no generated value ([expressions.inout-closure-parameters](08-expressions.md#expressions.inout-closure-parameters)). A property with E0332 reports nothing else.

Tests: [properties/declared.lt](../conformance/properties/declared.lt), [properties/holds.lt](../conformance/properties/holds.lt), [properties/inout_parameter.lt](../conformance/properties/inout_parameter.lt), [properties/not_a_closure.lt](../conformance/properties/not_a_closure.lt), [properties/untyped_parameter_and_mismatches.lt](../conformance/properties/untyped_parameter_and_mismatches.lt).

<a id="tests.property-checking"></a>
A property is checked as a doc example is ([program.doc-examples](04-programs.md#program.doc-examples)). Its names resolve as at module level, so no type parameter is in scope, and it may use `try`. Its closure's body must have type `bool`, or it is E0311, *mismatched types* ([types.mismatch](07-types.md#types.mismatch)). The body may raise an error type that implements `Show`, as a test's body may ([program.test-declarations](04-programs.md#program.test-declarations)). Any other error type is E0318, *unsatisfied bound* ([traits.unsatisfied-bounds](11-traits.md#traits.unsatisfied-bounds)). A property is exempt from every `without` limit, as test bodies and doc examples are ([facts.without](15-facts.md#facts.without)).

Tests: [properties/body_type.lt](../conformance/properties/body_type.lt), [properties/declared.lt](../conformance/properties/declared.lt), [properties/holds.lt](../conformance/properties/holds.lt), [properties/raise_without_show.lt](../conformance/properties/raise_without_show.lt), [properties/raises.lt](../conformance/properties/raises.lt), [properties/without_panic.lt](../conformance/properties/without_panic.lt).

<a id="tests.property-io"></a>
A property performs no `io`. The first call in its body that performs `io` is E0510, *property that performs `io`*, at the call ([effects.inference](12-effects.md#effects.inference)). So a property's cases, its counterexample and its verdict depend on its text alone ([tests.seeds](#tests.seeds)).

Tests: [properties/io.lt](../conformance/properties/io.lt).

## Types that can be generated

<a id="tests.generable-types"></a>
Each parameter's type must be **generable**, or it is E0333, *parameter type that can't be generated*, at the parameter's type. A type **holds** its elements, its fields, its payloads, a list's element type and a map's key and value types, and what those hold in turn. A type is generable when all three of these are true:

- it and every type it holds are built from `bool`, the numeric types ([numbers.numeric-types](06-numbers.md#numbers.numeric-types)), `str` and `()`, with tuples, lists, maps, records and variant types. The records and variant types may be those of the prelude or those that any module declares;
- neither it nor any type it holds is a function type, a type with no values ([patterns.types-without-values](09-patterns.md#patterns.types-without-values)) or a `Map<K, V>` whose `K` doesn't implement both `Eq` and `Hash` ([std.map-key-bounds](17-std.md#std.map-key-bounds)). `Never` and `type Loop = | Loop(Loop)` are types with no values;
- it holds finitely many types ([tests.growth-test](#tests.growth-test)).

Tests: [properties/generable.lt](../conformance/properties/generable.lt), [properties/ungenerable.lt](../conformance/properties/ungenerable.lt).

<a id="tests.growth-test"></a>
Whether a type holds infinitely many types is decided on a graph, without expanding any type. `Grow<i64>` holds infinitely many with `type Grow<T> = | Stop | More(Grow<List<T>>)`. The graph is this:

- **Nodes.** Each type parameter of each type declaration that the type holds, directly or through other declarations.
- **Edges.** Take a declaration `D<p1, …, pn>` whose fields or payloads hold `E<a1, …, am>`. For each argument `aj` and each parameter `pi` that occurs in `aj`, it gives an edge from `D.pi` to `E.j`. The edge **grows** when `pi` occurs strictly inside `aj`, as `T` does in `List<T>` or `(T, T)`, and doesn't when `aj` is `pi` itself. An argument that mentions no parameter gives no edge, so `type A<T> = | X | Y(A<i64>)` holds finitely many types.
- **The test.** A type holds infinitely many types exactly when this graph has a cycle with a growing edge.

Tests: [properties/generable.lt](../conformance/properties/generable.lt), [properties/ungenerable.lt](../conformance/properties/ungenerable.lt).

## Cases

<a id="tests.property-cases"></a>
A property runs at most 100 cases, numbered from 0 to 99, in order. It passes when every case passes, and fails at its first case that fails. Case 0 gives each parameter its minimal value ([tests.minimal-values](#tests.minimal-values)). Case `i`, for `i` from 1 to 99, generates the parameters' values in order, each with budget `i` and size `i` ([tests.generated-scalars](#tests.generated-scalars), [tests.composite-values](#tests.composite-values)). It generates them from the numbers that the case's generator draws ([tests.draws](#tests.draws)).

Tests: [properties/cases.lt](../conformance/properties/cases.lt), [properties/holds.lt](../conformance/properties/holds.lt).

<a id="tests.seeds"></a>
A property's **seed** is the 64-bit FNV-1a hash of its text in UTF-8. It starts from `0xcbf29ce484222325`. Then, for each byte, it exclusive-ors the byte in and multiplies by `0x100000001b3`, modulo 2⁶⁴. So a property's cases depend on its text alone. They are the same on every run and in every implementation, and change when the property does.

Tests: [properties/cases.lt](../conformance/properties/cases.lt), [properties/holds.lt](../conformance/properties/holds.lt).

<a id="tests.draws"></a>
Case `i` draws from a SplitMix64 generator whose state starts at the seed plus `i`, modulo 2⁶⁴. Each draw, `next()`, works modulo 2⁶⁴ in these steps:

1. It adds `0x9e3779b97f4a7c15` to the state.
2. It computes `z` from the new state by `z = (z ^ (z >> 30)) * 0xbf58476d1ce4e5b9`.
3. It computes `z = (z ^ (z >> 27)) * 0x94d049bb133111eb`.
4. It returns `z ^ (z >> 31)`.

`below(n)` is `next()` modulo `n`, and draws one number even when `n` is 1. A value's draws are made in the order that [tests.generated-scalars](#tests.generated-scalars) and [tests.composite-values](#tests.composite-values) write them. A value's components are generated in order.

Tests: [properties/cases.lt](../conformance/properties/cases.lt), [properties/holds.lt](../conformance/properties/holds.lt).

<a id="tests.generated-scalars"></a>
At size `s`, a value of a scalar type is:

| Type | Value |
| --- | --- |
| `bool` | `true` when `below(2)` is 1 |
| An integer type | By `k = below(4)`: when `k` is 0, a boundary value `B[below(n)]`, of the `n` values of the type's list `B` ([tests.boundary-values](#tests.boundary-values)); when `k` is 1 or 2, `below(2s + 1) - s` for a signed type, and `below(s + 1)` for an unsigned one; when `k` is 3, the low `w` bits of `next()` for a type of `w` bits, read as two's complement for a signed type |
| A float type | By `k = below(4)`: when `k` is 0, a boundary value, as for integers; when `k` is 1 or 2, the integer `below(512s + 1) - 256s` divided by 256, which is exact; when `k` is 3, the value whose bits are those of `next()` for `f64`, and its low 32 bits for `f32` |
| `str` | `n = below(s + 1)` scalar values, each by `k = below(4)`: when `k` is 0 or 1, the value `0x20 + below(95)`; when `k` is 2, `below(128)`; when `k` is 3, `v = below(0x10F800)`, plus `0x800` when `v` is at least `0xD800`, which skips the surrogates |
| `()` | `()`, with no draw |

Tests: [properties/cases.lt](../conformance/properties/cases.lt), [properties/holds.lt](../conformance/properties/holds.lt).

<a id="tests.boundary-values"></a>
The boundary values of a type, in this order, are:

- for a signed integer type: 0, 1, -1, `MIN`, `MAX`, `MIN + 1` and `MAX - 1`;
- for an unsigned integer type: 0, 1, `MAX` and `MAX - 1`;
- for a float type: `0.0`, `-0.0`, `1.0`, `-1.0`, the largest finite value and its negation, the smallest positive normal value, the smallest positive subnormal value, `INFINITY`, `-INFINITY` and `NAN` ([std.floats](17-std.md#std.floats)).

Tests: [properties/cases.lt](../conformance/properties/cases.lt), [properties/holds.lt](../conformance/properties/holds.lt).

<a id="tests.composite-values"></a>
At budget `b`, a value with `k` components gives each component a budget. The budget is `(b - 1) / k`, rounded down, when `b` is at least 1, and 0 when `b` is 0. Its scalars take the case's size, whatever their budget.

| Type | Value at budget `b` |
| --- | --- |
| A tuple or a record | Its elements or fields, in order ([records.field-order](07-types.md#records.field-order)): `k` components |
| `List<T>` | `n = below(b + 1)`, then `n` elements, in order: `k` is `n` |
| `Map<K, V>` | `n = below(b + 1)`, then `n` entries, each a key then a value, inserted in order, so that a key equal to an earlier one replaces its value and keeps its place ([std.maps](17-std.md#std.maps)): `k` is `2n`. Inserting calls the key type's `hash` and `eq`, so with written impls that break the law between them, or an `eq` that can panic, the map generated is unspecified ([traits.hash-follows-written-eq](11-traits.md#traits.hash-follows-written-eq)) |
| A variant type | When `b` is at least 1, its variant number `below(m)`, in declaration order, among its `m` variants whose payload types all have values; when `b` is 0, its variant number `below(m)` among its `m` nearest variants ([tests.minimal-values](#tests.minimal-values)). Then that variant's payloads, in order: `k` is their number |

Tests: [properties/generable.lt](../conformance/properties/generable.lt).

<a id="tests.minimal-values"></a>
A type's **depth** is the least nesting of tuples, records and variants in one of its values:

- a scalar type, a list type and a map type have depth 0;
- a tuple or record type has the depth one more than the greatest depth of its components, and 1 when it has none;
- a variant type has the depth one more than the least height of its variants whose payload types all have values.

A variant's **height** is the greatest depth of its payloads, and 0 when it has none. The variants of least height are the type's **nearest variants**. A type's **minimal value** is this:

- `false`, 0, `0.0`, `""`, `()`, the empty list or the empty map, for those types;
- the minimal values of its components, for a tuple or a record;
- for a variant type, its first nearest variant, in declaration order, with the minimal values of its payloads.

So a minimal value is finite, and generating a value ends.

Tests: [properties/cases.lt](../conformance/properties/cases.lt), [properties/generable.lt](../conformance/properties/generable.lt).

## Running and shrinking

<a id="tests.running-cases"></a>
A case calls the closure with the case's values. It passes when the closure returns `true`, and fails when it returns `false`, raises or panics. A stack overflow or running out of memory ends every test, as [program.test-results](04-programs.md#program.test-results) says.

Tests: [properties/failures.lt](../conformance/properties/failures.lt), [properties/raises.lt](../conformance/properties/raises.lt).

<a id="tests.shrinking"></a>
When a case fails, its values are **shrunk**. The shrinker starts from the case's values. It takes each parameter in order, and each candidate of that parameter's current value in the order of [tests.shrink-candidates](#tests.shrink-candidates). For each candidate, it runs the closure with the candidate in the value's place and the other values as they are. The first candidate whose run fails in the same way replaces the value, and the search starts again from the first parameter. A run fails in the same way when it does one of these:

- it returns `false` where the case returned `false`;
- it raises where the case raised, whatever it raises;
- it panics with the kind that the case panicked with.

Shrinking ends when a search over every parameter's candidates replaces nothing, or after 1,000 runs of the closure. The values it ends with are the **counterexample**.

Tests: [properties/failures.lt](../conformance/properties/failures.lt).

<a id="tests.shrink-candidates"></a>
A value's candidates are these, in order, leaving out each candidate identical to the value or to an earlier candidate. Identical values have one structure, with floats compared by their bits, whatever the types' `Eq` impls. So comparing candidates calls no code of the program.

| Value | Candidates |
| --- | --- |
| `true` | `false` |
| An integer `x` other than 0 | 0; `-x`, when `x` is negative and `-x` is in its type's range; `x / 2`, truncated toward zero; `x - 1` when `x` is positive, and `x + 1` when it is negative |
| A NaN or an infinite float | `0.0` |
| A finite float `x` | `0.0`; `-x`, when `x` is negative; `x.trunc()`; `(x / 2.0).trunc()`, when `x` is a whole number |
| A string of `n` scalar values | `""`; the string without its first `n / 2` scalar values, rounded down; the string with only those; the string without each one scalar value, from the first; the string with each scalar value other than `a` replaced by `a`, from the first |
| A list of `n` elements | `[]`; the list without its first `n / 2` elements, rounded down; the list with only those; the list without each one element, from the first; for each element, from the first, the list with each of that element's candidates in its place |
| A map | The candidates of the list of its entries, in insertion order, except that a key has no candidates, so that only values are shrunk in place |
| A tuple or a record | For each component, in order, the value with each of that component's candidates in its place |
| A value of the variant type `T` | `T`'s minimal value; each of the value's payloads whose type is `T`; for each payload, in order, the value with each of that payload's candidates in its place |

Every other value has no candidates.

Checked by: the tests of shrinking in both implementations, since conformance compares only whether a property passed: counterexamples shrunk by [tests.shrinking](#tests.shrinking) and this paragraph, in `interpreter/test/test_props.ml` and `compiler/stilt-cli/tests/properties.rs`, and `just differential`, which compares the counterexamples of generated programs' properties.

## Results

<a id="tests.property-results"></a>
A property is a doc example for every rule that names one. It is a body, checked in the phases that bodies are ([errors.phases](18-errors.md#errors.phases)). `stilt test` reports its result with the tests and examples of its file, in source order ([program.test-order](04-programs.md#program.test-order)). The result is a test object whose line is that of its `/// prop:` comment, which a `PASS` or `FAIL` entry on that line expects ([conformance.inline-annotations](01-conformance.md#conformance.inline-annotations)). `check` and `run` run no property. A property performs no `io`, so an implementation may reuse its cached result, as it may a test's ([program.running-tests](04-programs.md#program.running-tests)).

Tests: [properties/declared.lt](../conformance/properties/declared.lt), [properties/failures.lt](../conformance/properties/failures.lt), [properties/holds.lt](../conformance/properties/holds.lt), [properties/run_runs_none.lt](../conformance/properties/run_runs_none.lt).

<a id="tests.property-verdict"></a>
In `test --json`, a property's object has the field `property`. It is an object with `seed`, the property's seed in 16 lowercase hexadecimal digits, and `cases`, the number of cases it ran, 100 when it passed. When the property failed, the object also has these fields:

- `case`: the number of its case that failed;
- `counterexample`: one string for each parameter, its value in the counterexample, as [std.show-output](17-std.md#std.show-output) shows a value nested inside another. The value is written by its structure, even when its type's `Show` impl is written by the user;
- `failure`: `"false"`, `"raise"`, or `"panic: KIND"` with the panic's kind ([effects.panic-kinds](12-effects.md#effects.panic-kinds));
- `detail`: for a raise, the raised value as its `Show` impl shows it, and for a panic, its detail ([program.panic-detail](04-programs.md#program.panic-detail));
- `shrinks`: the number of values that shrinking replaced.

Every field is the same on every run and in every implementation, except the `detail` of a panic other than `explicit`, whose wording is up to the implementation.

Checked by: the tests of the `property` object, whose fields the conformance runner ignores: its seed, case, counterexample, failure, detail and shrinks, the same on every run, in `interpreter/test/test_props.ml` and `compiler/stilt-cli/tests/properties.rs`.

## Parts and addresses

<a id="edits.parts"></a>
A **part** is a declaration of a module, or the body of one. The declarations are these:

- the functions, types, traits, constants and tests at module level;
- the functions and constants of inherent impls;
- the methods that traits declare;
- the methods of trait impls.

A `use` declaration, a module header and an `impl` block as a whole are not parts. A declaration that doesn't exist has no address. A file's imports and header change, and a declaration is added, by writing the file.

Checked by: the toolchain's tests of `show --json` on each kind of declaration and body (`compiler/stilt-cli/tests/edits.rs`).

<a id="edits.bodies"></a>
The body of a function is its block, or its `= ?` ([declarations.typed-holes](10-declarations.md#declarations.typed-holes)). The body of a test is its block, and the body of a constant is its initializer, the expression after its `=`. These are the bodies of [errors.phases](18-errors.md#errors.phases), except doc examples and properties, which belong to their declaration. Types, traits, and a trait's method without a default body have no body.

Checked by: the toolchain's tests of `show --json` on each kind of body (`compiler/stilt-cli/tests/edits.rs`).

<a id="edits.extents"></a>
A declaration runs from its first doc comment, or from its first token when it has none, `pub` included, to its last token. A body runs from its first token to its last. Each holds the comments in its span, and a comment that follows its last token on the same line. So a declaration's doc comments, with their examples and properties, belong to it ([program.doc-comments](04-programs.md#program.doc-comments)).

Checked by: the toolchain's tests of hashes, which a comment inside a part and one after its last token change (`compiler/stilt-edit/src/tests.rs`, `compiler/stilt-cli/tests/edits.rs`).

<a id="edits.paths"></a>
A declaration's **path** is its module's name ([program.module-names](04-programs.md#program.module-names)), followed by:

| Declaration | Followed by | Example |
| --- | --- | --- |
| A function, type, trait or constant at module level | `.name` | `main.totals`, `orders.Order` |
| A test | `.` and its name as a string literal, quoted and escaped as `parse --sexp` prints strings ([syntax.tree-form](03-syntax.md#syntax.tree-form)) | `main."parses a line"` |
| A function or constant of an inherent impl of the type `T` | `.T.name` | `main.Point.norm`, `main.Stack.LIMIT` |
| A method that the trait `Tr` declares, with a default body or without one | `.Tr.name` | `main.Shape.area` |
| A method of the impl of the trait `Tr` for the type constructor `T` | `.T.Tr.name` | `main.Point.Show.show` |

`T` and `Tr` are the last names of the type constructor and the trait as the impl writes them, without a module's path. So `impl Pretty for orders.Order` in the module `pretty` gives `pretty.Order.Pretty.pretty`.

Checked by: the toolchain's tests of paths: every kind of declaration, a test name that needs escapes, and the impls of other modules' types and of primitive types (`compiler/stilt-cli/tests/edits.rs`).

<a id="edits.reading-paths"></a>
A path names each part whose path, by [edits.paths](#edits.paths), it is. Its module is never in doubt. The segments of a module's name are lowercase and never a primitive type's name ([program.module-names](04-programs.md#program.module-names)). A type's or a trait's name in a path is uppercase or a primitive type's. So `pretty.Order.Pretty.pretty` names a method of the module `pretty`, though `pretty` declares no `Order`. An item that hides a child module of its name in code ([program.child-modules](04-programs.md#program.child-modules)) hides none of that module's parts.

Checked by: the toolchain's tests of paths, a part of a module that an item of its parent hides in code among them (`compiler/stilt-cli/tests/edits.rs`).

<a id="edits.body-addresses"></a>
`PATH/body` names the body of the declaration at `PATH`, as `main.totals/body`.

Checked by: the toolchain's tests of body addresses (`compiler/stilt-cli/tests/edits.rs`).

<a id="edits.one-part-per-path"></a>
A path names at most one declaration. Names are unique in each namespace of a module ([declarations.unique-names](10-declarations.md#declarations.unique-names)), across the inherent blocks of a type ([traits.inherent-names](11-traits.md#traits.inherent-names)) and among a module's tests ([program.test-declarations](04-programs.md#program.test-declarations)). A trait has at most one impl per type constructor ([traits.coherence](11-traits.md#traits.coherence)). There are three exceptions:

- a type or a trait and a constant of one name, which live in different namespaces ([declarations.namespaces](10-declarations.md#declarations.namespaces));
- two impls of one trait in one module, for type constructors of one name from different modules;
- two declarations that break one of those rules, in a program with that error.

Given a path that names two declarations, `stilt show` shows each of them, with its hash. An edit addressed by such a path applies to the one whose hash the address gives ([edits.hash](#edits.hash)), so the fix of a duplicate name can rename either declaration. The address is ambiguous only when both declarations have that hash, and an edit addressed by it is refused with E0702 ([edits.refusals](#edits.refusals)).

Checked by: the toolchain's tests of paths that name two parts: a type and a constant, a trait and a constant, two impls for other modules' types of one name, and two functions of one name in a program with that error, shown and refused (`compiler/stilt-cli/tests/edits.rs`).

## Hashes

<a id="edits.canonical-text"></a>
A part's **canonical text** is the text that `stilt fmt` writes for its syntax tree and its comments ([syntax.format](03-syntax.md#syntax.format)) when the part stands alone. It starts at column 0, at the outermost level of indentation, with `\n` ending each line but the last, and no newline after it. It depends on the part alone: never on where the source breaks lines, on the part's indentation in its file, or on anything outside the part. So formatting a file, moving a method into another block or changing a signature leaves the body's hash unchanged.

Checked by: the toolchain's tests of canonical text (`compiler/stilt-edit/src/tests.rs`, `compiler/stilt-cli/tests/edits.rs`).

<a id="edits.hash"></a>
A part's **hash** is the first four hexadecimal digits, in lowercase, of the BLAKE3 digest of its canonical text in UTF-8. They are the digest's first two bytes. An address with a hash is written `PATH#hash` or `PATH/body#hash`, as `main.totals/body#a91f`.

Checked by: the toolchain's tests of hashes, unchanged by `stilt fmt`, by reindenting a file, by moving a method between blocks and by editing a signature, and changed by a comment in the part (`compiler/stilt-edit/src/tests.rs`, `compiler/stilt-cli/tests/edits.rs`).

<a id="edits.files-with-syntax-errors"></a>
In a file with a syntax error, the parts are those of the items that the file's parts declare ([syntax.parts](03-syntax.md#syntax.parts), [errors.parts](18-errors.md#errors.parts)). They are at module level and inside the blocks of its traits and impls. A declaration whose item parses has the address and hash of the paragraphs above. The item that a part with an error declares has the path of [edits.paths](#edits.paths). It has no canonical text. Its hash is that of [edits.hash](#edits.hash), computed over its source text exactly as written, from its first doc comment or token to the end of the part's text without the blank lines and the lines that are only a comment that end it. So the text after a lexical error ([syntax.lexical-errors](03-syntax.md#syntax.lexical-errors)), which yields no tokens, is the declaration's too. It has no `/body`. So a declaration that doesn't parse can be replaced as a whole, by its address.

Checked by: the toolchain's tests of parts in files with syntax errors, an item addressed and replaced as a whole and its `/body` refused, and an item with a lexical error running to the end of its text (`compiler/stilt-cli/tests/edits.rs`, `compiler/stilt-edit/src/tests.rs`).

## Showing parts

<a id="edits.showing-parts"></a>
`stilt show ADDRESS [PATH]` takes the address of any part, of the program, of `std` or of a dependency, with or without a hash. An address with a hash is refused, as an edit would be ([edits.refusals](#edits.refusals)), unless its hash is the part's current one. With `--json`, the record of a declaration has these fields, beside its others:

- `at`, its address with its current hash, as `"at": "main.label#3f9a"`;
- `text`, its canonical text, which the hash covers;
- `body`, for a declaration with a body, the body's address with its current hash.

The record of a body has `at` and `text`, and a module's record holds the records of all its declarations.

Checked by: the toolchain's tests of `show` with an address: the `at`, `text` and `body` fields, and a stale hash refused (`compiler/stilt-cli/tests/edits.rs`).

<a id="edits.diagnostic-addresses"></a>
In `check --json` and `test --json`, a diagnostic whose primary span lies in a part has the field `at`. It is the address, with its current hash, of the smallest part that holds the span: the body when the span lies in one, and the declaration otherwise. A diagnostic outside every part has no `at`. Among these are the diagnostics in a `use` declaration, in a module header, in a manifest, and in the header of an `impl` block from its `impl` keyword to its `{`.

Checked by: the toolchain's tests of `at` in diagnostics: in a body, in a signature, in a doc example, in a `use` declaration and at an impl's header (`compiler/stilt-cli/tests/edits.rs`).

## Edits

<a id="edits.command-line"></a>
`stilt check` and `stilt test` take edits:

```text
stilt check [--json] [--edit ADDRESS TEXT]… [PATH]
stilt test  [--json] [--edit ADDRESS TEXT]… [PATH]
```

`ADDRESS` is an address with its hash. `TEXT` is the part's new text, or `-`, which reads it from standard input, as at most one edit may. `PATH` is the program, as the command-line protocol gives it ([conformance.paths](01-conformance.md#conformance.paths)), and the working directory when it is left out. The edits apply as [edits.all-or-nothing](#edits.all-or-nothing) says. The command then gives its verdict on the edited program, as it does without edits.

Checked by: the toolchain's tests of the command line of `check` and `test`, an edit of each kind of part from the command line and from standard input, and `test --edit` running the edited program's tests (`compiler/stilt-cli/tests/edit_apply.rs`).

<a id="edits.new-text"></a>
An edit's text is lexed as a file is ([Lexical structure](02-lexical.md)). It must then parse as exactly one instance of the part, with nothing else around it but blank lines:

- **A declaration** takes one declaration of the same kind, function, type, trait, constant or test, with the doc comments it is to have. The declaration is in the grammar of its place. That is an `item` at module level, an `inherent_member` in an inherent impl and a `trait_impl_member` in a trait impl ([syntax.programs](03-syntax.md#syntax.programs)). It is a `trait_member` in a trait ([syntax.declarations](03-syntax.md#syntax.declarations)). Its doc examples and properties must parse. It may give the declaration another name, and with it another address.
- **A function's body** takes a `fn_body`: a block, or `= ?`.
- **A test's body** takes a `block` ([syntax.blocks](03-syntax.md#syntax.blocks)), and **a constant's body** an `expr` ([syntax.expressions](03-syntax.md#syntax.expressions)).

Checked by: the toolchain's tests of the text an edit takes, a rename among them (`compiler/stilt-edit/src/tests.rs`, `compiler/stilt-cli/tests/edit_apply.rs`).

<a id="edits.refusals"></a>
An edit is **refused**, with one of these codes, when it:

| Code | Refusal |
| --- | --- |
| E0700, *malformed edit* | is malformed: its address isn't a path of [edits.paths](#edits.paths), with `/body` or without it, then `#` and four lowercase hexadecimal digits; or it is a second edit that reads standard input |
| E0701, *address that names no part* | names no part of the program's own files: nothing has its path, the declaration has no body, or the part lies in `std` or in a fetched dependency ([packages.dependencies-with-errors](04-programs.md#packages.dependencies-with-errors)) |
| E0702, *ambiguous address* | names two parts ([edits.one-part-per-path](#edits.one-part-per-path)) |
| E0703, *stale address* | carries a hash other than the part's current hash, since the part has changed since its author read it |
| E0704, *edit that doesn't parse as its part* | has a text that doesn't parse as the part ([edits.new-text](#edits.new-text)) |
| E0705, *overlapping edits* | overlaps another edit: both address one part, or one addresses a declaration and the other its body |

The registry checks refusals under `refusal` ([errors.registry-phases](18-errors.md#errors.registry-phases)), before the program. Each comes with no diagnostic of the program, which none of them changes.

Checked by: the toolchain's tests of each refusal, with every file left byte for byte as it is, and edits of a part of `std`, of a fetched dependency and of a path dependency (`compiler/stilt-cli/tests/edit_apply.rs`), and the snapshots of `tests/diagnostics/`, since the command-line protocol gives no edits.

<a id="edits.all-or-nothing"></a>
Every edit is checked against the files as they are before any of them applies. If any edit is refused, none applies, no file changes, and the command gives no verdict. It reports each edit's result and exits with status 2, as `show` does for an address that names nothing. Otherwise every edit applies.

Checked by: the toolchain's tests of edits applied all or none: two edits where one is refused, neither applied, and two edits of different parts of one file, both applied (`compiler/stilt-cli/tests/edit_apply.rs`).

<a id="edits.writing"></a>
An edit replaces the part's source text with the new text, written as `stilt fmt` writes it in the part's place, at the part's indentation. It leaves every byte of the file outside the part as it is. A command whose edits apply writes the pins of `docs.lock` too, for the package of each file it edits ([docs.writing-pins](04-programs.md#docs.writing-pins)).

Checked by: the toolchain's tests of writing, the bytes outside an edited part unchanged in a file that isn't canonical (`compiler/stilt-cli/tests/edit_apply.rs`).

<a id="edits.concurrent-edits"></a>
Between checking an edit's hash and writing its file, no other command writes the file. So of two commands that edit one part from one hash, one applies, and the other is refused with E0703.

Checked by: the toolchain's tests of two processes editing one part from one hash, of which exactly one applies (`compiler/stilt-cli/tests/edit_apply.rs`).

<a id="edits.edit-results"></a>
Each edit has a result. With `--json`, the results are the list `edits` of the object that the command writes, in the order of the command line. Each result is an object with these fields:

- `at`: the address as the edit gave it;
- `applied`: `true` or `false`;
- `now`: the part's address with its hash after the command, which is the new hash when the edit applies and the current one when it is refused. It is absent when no single part has the edit's path, after E0700, E0701 or E0702;
- `refused`: the code of the refusal, when the edit is refused;
- `syntax`: after E0704, when the text has a syntax error, the `code`, `line` and `col` of its first one ([syntax.first-error](03-syntax.md#syntax.first-error)), counted within the text.

When an edit is refused, the object holds only `edits`, with neither `diagnostics` nor `tests`. Without `--json`, each refusal is rendered as a diagnostic on stderr. It is placed at `command line`, or, for one about an edit's text, at `edit N`, the edit's position on the command line. Each edit that applies writes `applied ADDRESS -> #HASH` to stderr before the verdict.

Checked by: the toolchain's tests of the results of edits, the `now` that each refusal reports among them (`compiler/stilt-cli/tests/edit_apply.rs`).

## Edits in verdicts

<a id="edits.json-form"></a>
An edit is the object `{"at": ADDRESS, "new": TEXT}`: its address with its hash, and the part's whole new text, in canonical format. `--edit` applies it with the two fields as they are: `stilt check --edit AT NEW`.

Checked by: the toolchain's tests of the JSON form of an edit (`compiler/stilt-cli/tests/edit_apply.rs`, `compiler/stilt-cli/tests/edit_fixes.rs`).

<a id="edits.fixes-as-edits"></a>
Each fix that a diagnostic offers is an object of the diagnostic's list `fixes`. It has `title`, the fix's description in one line, as its message gives it. It has `edits`, the edits that make its change, one for each declaration it changes, so that no two overlap (E0705). Each edit addresses the declaration's body when every change that the fix makes in the declaration lies in the body, and the declaration otherwise. It carries the part's current hash, and gives the part's whole text with the fix applied. Applying a fix's edits with one `check` gives a program that reports that diagnostic's code in none of those parts.

A fix has no edits when it changes text outside every part, as in a `use` declaration, a module header, an impl's header or a manifest. It has none either when it changes a part whose path names two parts. Its message still shows its change.

Checked by: the toolchain's tests of fixes as edits (`compiler/stilt-cli/tests/edit_fixes.rs`), and every fix of every snapshot in `tests/diagnostics/`, applied through `--edit` (`compiler/stilt-cli/tests/snapshots.rs`).

## The REPL

<a id="repl.sessions"></a>
`stilt repl` starts a **session** of the REPL on the program in the working directory. A directory that holds `main.lt` is a directory program, and one that holds `stilt.toml` a package ([program.forms](04-programs.md#program.forms)). When the program has errors, the session reports its diagnostics first, rendered as `check` renders them, as `run` does ([program.programs-with-errors](04-programs.md#program.programs-with-errors)). With no program there, the session's program has one module, `main`, which declares nothing, so its inputs see the prelude alone.

Checked by: the toolchain's tests, which drive sessions through standard input (`compiler/stilt-cli/tests/repl.rs`), since the command-line protocol's `run PATH` starts no session.

<a id="repl.scope"></a>
An input is checked in the scope of the session's module, `main` when the session starts. That scope holds the module's items, the modules it imports with `use`, and the prelude ([program.what-use-binds](04-programs.md#program.what-use-binds), [program.contents](04-programs.md#program.contents)). The session's bindings are in scope as a body's locals are, so a binding hides an item of the same name. `:module NAME` makes the module `NAME` of the program, or of the standard library, the session's module. The next inputs see its private items, and the bindings stay. A name that is no module is refused with a message, and the session's module stays.

Checked by: the toolchain's tests of sessions (`compiler/stilt-cli/tests/repl.rs`).

<a id="repl.inputs"></a>
Each line of standard input, without the spaces around it, is an **input**, numbered from 1 in the order read. An empty line is skipped. An input that starts with `:` is a command. `:module NAME` is the only command, and any other is refused with a message. Any other input must be one statement ([syntax.statements](03-syntax.md#syntax.statements)), with no separator after it but `;`, and the statement must be an expression or a `let`:

- **Declarations.** An input that parses as the declarations of a file is refused with a message. Declarations stay in the program's files, where the session reads them ([repl.program-edits](#repl.program-edits)).
- **Other statements.** A `var`, an assignment or an `assert` is refused with a message.
- **Syntax errors.** An input that doesn't parse as a statement has a syntax error, its first, reported as [repl.input-checking](#repl.input-checking) places it.

An input that reads standard input, as `read_line()` does, reads the session's next line.

Checked by: the toolchain's tests of sessions (`compiler/stilt-cli/tests/repl.rs`).

<a id="repl.input-checking"></a>
An input is checked as a test's body of the session's module is ([program.test-declarations](04-programs.md#program.test-declarations)), with each binding at the type that its `let` gave it. It may perform `io` and raise any error whose type implements `Show`, and a call that can raise is marked with `try` ([effects.marking](12-effects.md#effects.marking)). Its type is the type of its last expression, which a `return` in it gives too. An input that can't end, as `exit(0)`, has type `Never`. Its diagnostics, of every phase ([errors.phases](18-errors.md#errors.phases)), are rendered as `check` renders them, placed at `input N`. So `input 3:1:7` is line 1, column 7 of the third input. An input with an error, or that meets the error type ([errors.error-type](18-errors.md#errors.error-type)), isn't run and changes no binding. An input with warnings runs, after them.

Checked by: the toolchain's tests of sessions (`compiler/stilt-cli/tests/repl.rs`).

<a id="repl.answers"></a>
An expression answers with its value and its type, `VALUE: TYPE`, on stdout. The value is shown as `show_nested` shows it, so a string is quoted ([traits.show](11-traits.md#traits.show), [std.show-output](17-std.md#std.show-output)). The type is written as a program writes it, each type by its own name. A value whose type doesn't implement `Show`, such as a function, answers with its type alone. A `let` answers with each name it binds, in the order its pattern binds them, and its type, `NAME: TYPE`, one per line. It binds them in the session, where a name bound again replaces its binding. What an input prints comes before its answer.

Checked by: the toolchain's tests of sessions (`compiler/stilt-cli/tests/repl.rs`), and `just latency`, which times answers.

<a id="repl.running-inputs"></a>
An input without errors is compiled into the session's image, with the code of the program that it reaches, which the image compiles once. It runs on a thread of its own. A raise that ends the input reports `error: {e}` on stderr, as one that escapes `main` does ([program.exit-statuses](04-programs.md#program.exit-statuses)). A panic ends the input with the report of [program.panic-report](04-programs.md#program.panic-report) on stderr. The report's `at` line is left out when the panic is located in the input itself. An input that a raise or a panic ends binds no name, so the binding of a name that its `let` binds stays as it is. A call of `exit` ends the session with its status. A stack overflow or running out of memory ends the session as it ends a program, with status 134 ([program.exit-statuses](04-programs.md#program.exit-statuses)).

Checked by: the toolchain's tests of sessions (`compiler/stilt-cli/tests/repl.rs`).

<a id="repl.program-edits"></a>
Before each input, the session takes in the edits made to the program's files since the input before, as `run` does. Every function of the program that the session's inputs reach is called through a slot that holds its latest code. So each later call of an edited function runs its new code. An edit that leaves the program with errors is taken in too. Its code with an error panics with `check-error` where it is reached ([program.bodies-with-errors](04-programs.md#program.bodies-with-errors)). The program's diagnostics are reported before the input's answer, once for each version of them that holds an error.

Checked by: the toolchain's tests of sessions, which edit the program's files between inputs (`compiler/stilt-cli/tests/repl.rs`).

<a id="repl.bindings-across-edits"></a>
Bindings keep their values across edits, but a binding whose type changed is dropped, with a note on stderr that names it and its type. A binding's type changes when a declaration that it depends on is removed or changed. These are the declarations of the types that the type names, and of the types that their fields and payloads name in turn. A type that holds a function type changes with any change to the declaration of any type or trait. A closure holds values of types that its type doesn't name.

Checked by: the toolchain's tests of sessions, which edit the program's files between inputs (`compiler/stilt-cli/tests/repl.rs`).

<a id="repl.prompt-and-end"></a>
When standard input is a terminal, `> ` is written to stdout before each input. The session ends at the end of standard input, with status 0, unless an input ends it first ([repl.running-inputs](#repl.running-inputs)). A session on a program checks and lowers its inputs in the program's engine, the query database that the program's commands and the language server share. That engine doesn't stop for idleness while a session is open. The session's values and its image are in the process of `stilt repl`.

Checked by: the toolchain's tests of sessions, one of them on an engine with a short idle time, which answers after waiting longer than that (`compiler/stilt-cli/tests/repl.rs`).

<a id="repl.no-one-shot-evaluation"></a>
`stilt repl` takes no expression on its command line: tests, doc examples and properties evaluate code once.

Checked by: the toolchain's tests of sessions, where the command line refuses `repl --eval` (`compiler/stilt-cli/tests/repl.rs`).

## Engines

<a id="engines.private"></a>
A program's **engine** is the process that holds the program's query database between its commands, the sessions of the REPL on it and the language server. Each of them answers from what the ones before computed. An engine answers only the user who started it:

- It listens on a socket open to the user alone, in a directory of the user's own under the system's temporary directory that no other user may open. A command or an engine that finds the directory open to others closes it first.
- Some systems tell each end of a socket which user runs the other, Linux and macOS among them. On these, an engine answers no process of another user, and a command asks no engine of another user.
- When the directory belongs to another user, or isn't a directory, as a link isn't, a command uses no engine. It says so on stderr and runs in its own process, which gives the report that an engine gives, and `stilt engine` refuses to start.

Checked by: the toolchain's tests of engines, which find the directory and the socket closed to other users, open the directory to them or replace it with a link before a command (`compiler/stilt-cli/tests/engine_access.rs`), and the tests of the checks of the directory and of the user at the other end of a connection (`compiler/stilt-cli/src/engine/private.rs`).

<a id="engines.toolchains"></a>
A command is answered only by an engine of its own build of `stilt`. Each version that `stilt --version` prints has engines of its own, so commands of two versions on one program each start and use an engine of their version. An engine tells a command of another build of the same version by the path and the time of change of the command's executable. Such a command gets no answer: it runs in its own process, and the engine stops, so that the next command starts an engine of its build. A language server whose own executable another build replaces while it runs, as an update does, can reach no engine of its build: it stops, with a message that says why, and the editor starts the new build's.

Checked by: the toolchain's tests of engines, which run a command through a second link to the compiler's executable (`compiler/stilt-cli/tests/engine_access.rs`), and the tests of the names of engines' sockets (`compiler/stilt-cli/src/engine/place.rs`).
