# 16. Macros, staging and reflection

A program's compilation matches, checks or runs four kinds of code. Pattern macros match a use's tokens against arms and substitute a template. Staging annotations mark the parts of a body known at compile time. Reflection lets one generic body read the shape of the type that instantiates it. Procedural macros are compile-time functions from syntax to syntax. Pattern macros belong to the advanced tier, and the rest to the meta tier. [Syntax](03-syntax.md) gives the productions of macros, quotes and annotations, [Types](07-types.md) value parameters and polymorphic arguments, and [Traits](11-traits.md) bounds.

## Pattern macros

<a id="macros.syntax-declarations"></a>
`syntax name { arm … }` declares a **pattern macro** (the `syntax` production, [syntax.macros](03-syntax.md#syntax.macros)). A pattern macro is an item with a `lower` name in the value namespace, beside functions and constants. Declaring a function and a macro of the same name in one module is E0208, *name defined twice* ([declarations.namespaces](10-declarations.md#declarations.namespaces)). A pattern macro may be `pub`, take doc comments and be named from another module as a function is, as `tools.greet!("Ada")`. Its arms are separated by newlines or `;`, and each is a pattern, `=>` and a template.

A `pub` macro's patterns are part of its package's API, as a function's signature is, and its templates are its body. This holds for the checks of the API ([versions.api](21-versions.md#versions.api)) and for pinned docs ([docs.pins](04-programs.md#docs.pins)). Pattern macros belong to the advanced tier ([macros.advanced-tier](#macros.advanced-tier)).

Tests: [macros/across_modules/main.lt](../conformance/macros/across_modules/main.lt), [macros/expressions.lt](../conformance/macros/expressions.lt).

<a id="macros.patterns"></a>
An arm's pattern is a group, `( … )` or `[ … ]`, of **matchers**, optionally followed by one `$name: block`, the arm's **trailing block**. A matcher is one of:

- a **fragment**, `$name: kind`, whose kind is `expr`, `block`, `pattern`, `type`, `name`, which matches a `lower` identifier, or `Name`, which matches an `Upper` one;
- a **repetition**, `$( matchers ) sep op`, where `sep` is `,`, `;` or nothing, and `op` is `*`, for zero or more rounds, or `+`, for one or more;
- a group, `( … )`, `[ … ]` or `{ … }`, of matchers;
- any other token, which matches itself.

Tests: [macros/expressions.lt](../conformance/macros/expressions.lt), [macros/repetitions.lt](../conformance/macros/repetitions.lt).

<a id="macros.pattern-checks"></a>
A pattern must keep these rules:

- A fragment's name is given once in its pattern, and its kind is one of the six.
- An `expr`, `pattern` or `type` fragment is followed in its pattern by the end of its group, a `,`, a `;` or `=>`.
- A repetition holds at least one fragment.
- A trailing block's kind is `block`.

Next to a repetition, what follows a matcher is this:

- A matcher before a repetition is followed by the repetition's first matcher and, when its operator is `*`, by what follows the repetition.
- A repetition's last matcher is followed by its separator, or by its first matcher when it has none, and by what follows the repetition.

So `$($e: expr)*` breaks the rule for an `expr` fragment. A pattern that breaks one of these rules is E0220, *malformed macro pattern*, at the fragment or at the repetition's `$`.

Tests: [macros/declaration_errors.lt](../conformance/macros/declaration_errors.lt).

<a id="macros.templates"></a>
An arm's template is the tokens after its `=>`, up to the separator that ends the arm. So a template that spans lines is wrapped in a group, as `{ … }`. In a template, `$name` stands for the fragment that the pattern binds. `$( … ) sep op` repeats its contents once for each round of the pattern's repetition whose fragments it names, with `sep` between the rounds. A template must keep these rules:

- It names only fragments that its pattern binds, each inside exactly as many repetitions as it was bound in. So a fragment bound outside every repetition can't be named inside one.
- The fragments that one repetition of the template names come from one repetition of the pattern.
- Each repetition of the template names a fragment.

A template that breaks one of these rules is E0221, *malformed macro template*, at the fragment or at the repetition's `$`. `$` stands nowhere but in a `syntax` declaration and in a quote ([macros.splices](#macros.splices)). Anywhere else it is E0100, *syntax error*.

Tests: [macros/declaration_errors.lt](../conformance/macros/declaration_errors.lt), [macros/dollar.lt](../conformance/macros/dollar.lt), [macros/expressions.lt](../conformance/macros/expressions.lt), [macros/repetitions.lt](../conformance/macros/repetitions.lt).

<a id="macros.checked-templates"></a>
Each template is parsed where the macro is declared, with each fragment standing as one form of its kind. A template that parses as neither an expression nor a pattern is E0221, *malformed macro template*, at its first token. A macro whose every template parses as an expression is used where an expression stands ([macros.uses](#macros.uses)). A macro whose every template parses as a pattern is used where a pattern stands, and a macro may be both. The names a template writes are resolved where the macro is declared ([macros.hygiene](#macros.hygiene)). So a name that names nothing there is E0211, *unknown name*, at the declaration, and never at a use.

Tests: [macros/broken_template](../conformance/macros/broken_template/), [macros/declaration_errors.lt](../conformance/macros/declaration_errors.lt), [macros/patterns.lt](../conformance/macros/patterns.lt), [macros/use_errors.lt](../conformance/macros/use_errors.lt).

<a id="macros.uses"></a>
A **use** of a macro is a path, `!`, and a group, `( … )` or `[ … ]`, of balanced tokens (the `macro_use` production, [syntax.macro-uses](03-syntax.md#syntax.macro-uses)). The group may be followed on the same line by a `{ … }` group, the use's trailing block. A use in a head doesn't take a trailing block ([expressions.heads](08-expressions.md#expressions.heads)). A use stands where an expression or a pattern may. Its macro must be one whose templates are all of that form, or the use is E0223, *macro out of place*, at its path.

The grammar reads the groups as tokens. The path is resolved as a function's name is, so `unless!` names the macro `unless` and nothing else, and a local of that name doesn't hide it. A path that names no macro is E0211, *unknown name*. A path that names something else, and a macro's name written without `!`, are E0212, *wrong kind of name* ([declarations.wrong-kind-of-name](10-declarations.md#declarations.wrong-kind-of-name)). An arm written `( … )` matches only a use written `m!( … )`, and one written `[ … ]` only `m![ … ]`.

Tests: [macros/across_modules/main.lt](../conformance/macros/across_modules/main.lt), [macros/expressions.lt](../conformance/macros/expressions.lt), [macros/patterns.lt](../conformance/macros/patterns.lt), [macros/use_errors.lt](../conformance/macros/use_errors.lt).

<a id="macros.matching"></a>
A use's tokens are matched against the arms in order, and the first arm that matches them all is used. Matching doesn't go back into an arm once one of its fragments has matched. Within an arm:

- a fragment matches the longest form of its kind that its follower allows;
- a repetition runs as many rounds as it can, stopping before a separator that no further round follows;
- a trailing block matches the use's trailing block, so an arm without one matches only a use without one.

A use that no arm matches is E0222, *use that no arm matches*, at the furthest token that any arm reached. Its message says what that arm expected there, as a closing bracket that came too soon, or no trailing block. A macro whose declaration has an error expands no use, and reports nothing at its uses.

Tests: [macros/broken_template](../conformance/macros/broken_template/), [macros/expressions.lt](../conformance/macros/expressions.lt), [macros/repetitions.lt](../conformance/macros/repetitions.lt), [macros/use_errors.lt](../conformance/macros/use_errors.lt).

<a id="macros.expansion"></a>
The template of the arm that matched, each fragment replaced by the form it matched, replaces the use. It is then resolved and checked as code written there. Each fragment stays one form, as if parenthesized, so `$x * 2` with `$x` matching `1 + 2` is `(1 + 2) * 2`. A fragment that the template names twice is evaluated twice, as written.

Tests: [macros/expressions.lt](../conformance/macros/expressions.lt), [macros/repetitions.lt](../conformance/macros/repetitions.lt).

<a id="macros.hygiene"></a>
A pattern macro's expansion is hygienic. A name that the template binds, by `let`, `var`, a pattern, a closure's parameter or a `for`, is fresh. No name the user wrote refers to it, and it hides none of the user's. Any other name that the template writes resolves where the macro is declared, among the items and imports of its module, private ones included. What the using module declares or imports doesn't change where it resolves. The tokens of a fragment resolve where the use is, as the user wrote them, so a fragment can't name a binding that the template made. So in `syntax swap { ($a: name, $b: name) => { let tmp = $a; $a = $b; $b = tmp } }`, the template's `tmp` never captures the user's, and `swap!(tmp, y)` swaps the user's two variables.

Tests: [macros/across_modules/main.lt](../conformance/macros/across_modules/main.lt), [macros/hygiene.lt](../conformance/macros/hygiene.lt).

<a id="macros.advanced-tier"></a>
A module that declares a pattern macro is in the advanced tier ([program.module-tier](04-programs.md#program.module-tier)). A module that only uses one declared elsewhere stays in its tier, whatever forms the expansion writes, as one that only calls a method of an advanced trait does ([traits.advanced-tier](11-traits.md#traits.advanced-tier)).

Checked by: the facts suite, whose `tests/facts/macros.lt` carries `//~ tier: advanced` and whose two-module program `tests/facts/macro_uses/` keeps the module that only uses a macro in core, which `just facts` checks (`compiler/stilt-cli/tests/facts.rs`).

## Staging annotations

<a id="meta.staging-annotations"></a>
`comptime` before a `for`, an `if` or a `match` makes a **staging annotation** ([syntax.staging-annotations](03-syntax.md#syntax.staging-annotations)). There are four forms:

- `comptime for p in e { … }`;
- `comptime if c { … }`, with its `else if` and `else` branches;
- `comptime if let p = e { … }`;
- `comptime match e { … }`.

Each stands wherever the form it annotates may stand, and has its type. `comptime` before anything else is E0100, *syntax error*, and so is `comptime` after an `else`. The annotation of a chain is written once, before its first `if`, and covers the whole chain. Staging annotations belong to the meta tier ([meta.staging-tier](#meta.staging-tier)).

Tests: [staging/branches.lt](../conformance/staging/branches.lt), [staging/loops.lt](../conformance/staging/loops.lt), [staging/syntax_errors.lt](../conformance/staging/syntax_errors.lt).

<a id="meta.erasure"></a>
A staging annotation means what the form it annotates means. Deleting every `comptime` of a program that has no error changes none of its observables ([conformance.observables](01-conformance.md#conformance.observables)). A debug build runs each annotated form as if it weren't annotated. A release build may compute the annotated parts while it builds: it may unroll a `comptime for`, and keep one branch of a `comptime if` or a `comptime match`. It gives the observables of the program without its annotations.

A static expression that panics, as `n / 0` does, panics as that program does. It panics where the run reaches it, in every build, and never while the program is built or checked.

Tests: [staging/branches.lt](../conformance/staging/branches.lt), [staging/loops.lt](../conformance/staging/loops.lt), [staging/static_panic.lt](../conformance/staging/static_panic.lt).

Checked by: also the conformance runner, which runs each test whose program writes `comptime` and expects no diagnostic a second time, with every `comptime` deleted, and expects the same observables (`tools/runner/src/erased.rs`).

<a id="meta.static-expressions"></a>
These parts of an annotated form must each be a **static expression**:

- the iterable of a `comptime for`;
- the condition of every `if`, and the scrutinee of every `if let`, of a `comptime if`'s chain;
- the scrutinee of a `comptime match`, and the guards of its arms.

A static expression is one of these:

- a literal, or an interpolated string whose splices are static;
- a constant ([declarations.constant-declarations](10-declarations.md#declarations.constant-declarations)), or a value parameter in scope ([generics.value-parameters-in-body](07-types.md#generics.value-parameters-in-body));
- a variable that the pattern of an enclosing `comptime for`, `if let` of a `comptime if`'s chain, or arm of a `comptime match` binds. It is static within the body, the branch or the arm it binds for;
- a variable that a `let`, never a `var`, binds from a static value, the variables of its pattern included;
- a tuple, a list, a record, an anonymous record or a variant whose parts are static;
- a field, a tuple field or an index of a static value;
- `-`, `!` or a binary operator applied to static operands;
- a range whose bounds are static;
- a call of a function, a method, a trait's member or a variant named directly, whose receiver and arguments are static, and whose row is empty once its type parameters are instantiated. Its implicit effects don't count, so it may panic, allocate or diverge;
- a bound test, and the queries of reflection that [meta.static-reflection](#meta.static-reflection) lists.

Tests: [reflection/static.lt](../conformance/reflection/static.lt), [staging/branches.lt](../conformance/staging/branches.lt), [staging/static_expressions.lt](../conformance/staging/static_expressions.lt), [staging/static_panic.lt](../conformance/staging/static_panic.lt).

<a id="meta.not-static"></a>
Nothing else is static. Among the forms that aren't are a function's parameter, a `var`, a closure, a call through a function value, and a call whose row isn't empty, as `print(…)` or `fs.read(…)`. A block, an `if`, a `match`, a loop, `try` and `else` aren't static either.

An annotated part that isn't static is E0349, *staging annotation on a value known only at run time*. It is reported once, at its first part that isn't static in evaluation order ([values.left-to-right](05-values.md#values.left-to-right)). In that order, an expression's operands, callee, receiver and arguments come before the expression that holds them. So in `0..f(x)` with a parameter `x`, the error is at `x`, and in `print(1)` it is at the call. A block, an `if`, a `match`, a loop, a closure, `try` and `else` are reported whole, without looking inside them. The message names the reason: a parameter is known only at run time, a `var` may change, a call performs the effects of its row, and the other forms run code.

Tests: [reflection/static_errors.lt](../conformance/reflection/static_errors.lt), [staging/not_static.lt](../conformance/staging/not_static.lt).

<a id="meta.staged-loops"></a>
A `comptime for` iterates what a `for` iterates ([expressions.for-iterables](08-expressions.md#expressions.for-iterables)), a range, a list, a map or an array, when it is static. It also iterates the fields or the cases of a type ([meta.static-reflection](#meta.static-reflection)). Its variables are static in its body, but they are values, never type arguments. So `Array<i64, i>` in the body of `comptime for i` is E0347, *invalid value argument* ([generics.value-arguments](07-types.md#generics.value-arguments)).

Tests: [staging/errors.lt](../conformance/staging/errors.lt), [staging/loops.lt](../conformance/staging/loops.lt).

<a id="meta.annotated-code"></a>
The body of a `comptime for`, and the branches and arms of a `comptime if` or a `comptime match`, are ordinary code. They may read anything in scope and perform what the function's row allows. They may `break`, `continue` and `return` as the forms without annotations may. The patterns and arms of a `comptime match` are checked as a `match`'s are, its exhaustiveness included (E0329, *patterns that don't cover every value*, [patterns.non-exhaustive-matches](09-patterns.md#patterns.non-exhaustive-matches)).

Tests: [staging/branches.lt](../conformance/staging/branches.lt), [staging/errors.lt](../conformance/staging/errors.lt), [staging/loops.lt](../conformance/staging/loops.lt).

<a id="meta.staging-tier"></a>
A module that writes `comptime` is in the meta tier ([program.module-tier](04-programs.md#program.module-tier)).

Tests: [staging/loops.lt](../conformance/staging/loops.lt).

## Shapes

<a id="meta.std-meta"></a>
The module `std.meta` declares the native variant type `Shape<T>`, whose cases [meta.shapes](#meta.shapes) lists, and the native types of their accessors. A **native variant type** is a native type ([declarations.native-items](10-declarations.md#declarations.native-items)) whose cases patterns name, as a variant type's are, and which has no written representation. So it has none of the prelude's traits: no structural impl ([traits.structural-impls](11-traits.md#traits.structural-impls)) writes, compares or hashes a shape, and `"{i64.shape()}"` and `T.shape() == U.shape()` are E0318, *unsatisfied bound* ([traits.unsatisfied-bounds](11-traits.md#traits.unsatisfied-bounds)). `std.meta` also declares the values that procedural macros read and write ([macros.tokens-and-code](#macros.tokens-and-code)). It is not part of the prelude.

Tests: [reflection/shapes_have_no_impls.lt](../conformance/reflection/shapes_have_no_impls.lt), [reflection/shapes_integers.lt](../conformance/reflection/shapes_integers.lt), [reflection/shapes_scalars.lt](../conformance/reflection/shapes_scalars.lt).

<a id="meta.shape-and-name"></a>
In `std.meta`, and in a module that names it with `use`, two queries apply to every type `T` that may stand before `.` ([traits.functions-without-self](11-traits.md#traits.functions-without-self)). Such a type is a type parameter, a declared type or a primitive type:

- `T.shape()` is the shape of `T`, a value of type `meta.Shape<T>`;
- `T.name()` is `T`'s name as a diagnostic writes it, such as `"Point"` or `"List<i64>"`.

A function or a constant named `shape` or `name` that the type has is found first. It may be the type's own, come from a visible trait with an impl for the type, or come from a type parameter's bounds. In a generic body, `T.shape()` is resolved once, from `T`'s bounds, whatever type later instantiates `T`. In a module that doesn't name `std.meta`, `T.shape()` and `T.name()` are only what the type's members make them. So there, `T.shape()` on a type without a member `shape` is E0314, *no such method or member* ([traits.method-resolution](11-traits.md#traits.method-resolution)).

Tests: [reflection/broken_own_shape.lt](../conformance/reflection/broken_own_shape.lt), [reflection/impl_params.lt](../conformance/reflection/impl_params.lt), [reflection/names.lt](../conformance/reflection/names.lt), [reflection/names_without_meta.lt](../conformance/reflection/names_without_meta.lt), [reflection/shape_called_with_an_argument.lt](../conformance/reflection/shape_called_with_an_argument.lt), [reflection/shapes_integers.lt](../conformance/reflection/shapes_integers.lt), [reflection/shapes_scalars.lt](../conformance/reflection/shapes_scalars.lt), [reflection/trait_parameter_name.lt](../conformance/reflection/trait_parameter_name.lt).

<a id="meta.shapes"></a>
A type's shape is the first case of this table that fits it:

| Case | Types |
| --- | --- |
| `Int(meta.Integer<T>)` | Every integer type |
| `Float(meta.Convert<T, f64>)` | `f32` and `f64` |
| `Bool(meta.Convert<T, bool>)`, `Str(meta.Convert<T, str>)`, `Unit(meta.Convert<T, ()>)` | `bool`, `str` and `()` |
| `Option(meta.Convert<T, Option<E>>)` | `Option<E>` |
| `List(meta.Convert<T, List<E>>)`, `Set(meta.Convert<T, List<E>>)` | `List<E>`, and `Set<E>` as the list of its elements in insertion order |
| `Map(meta.Convert<T, List<(K, V)>>)` | `Map<K, V>`, as the list of its entries in insertion order |
| `Array(meta.Sized<T, E>)` | `array.Array<E, n>` ([generics.arrays](07-types.md#generics.arrays)) |
| `Tuple(meta.Fields<T>)` | Tuples, whose fields are named `"0"`, `"1"` and so on |
| `Record(meta.Fields<T>)` | Declared records, their fields in the order of their declaration, and anonymous records, their fields in alphabetical order ([records.field-order](07-types.md#records.field-order)) |
| `Variants(meta.Cases<T>)` | Declared variant types other than `Option`, `Result` among them |

A shape has no other case, and every other type has no shape ([meta.types-without-shape](#meta.types-without-shape)).

Tests: [reflection/let_else_on_a_shape.lt](../conformance/reflection/let_else_on_a_shape.lt), [reflection/shapes_cases.lt](../conformance/reflection/shapes_cases.lt), [reflection/shapes_collections.lt](../conformance/reflection/shapes_collections.lt), [reflection/shapes_fields.lt](../conformance/reflection/shapes_fields.lt), [reflection/shapes_integers.lt](../conformance/reflection/shapes_integers.lt), [reflection/shapes_scalars.lt](../conformance/reflection/shapes_scalars.lt).

<a id="meta.shape-accessors"></a>
In `Int(n)`, `n.text(value) -> str` is the decimal text of `value`. `n.parse(text: str) -> Option<T>` is `None` for text that isn't an integer of `T`'s range written as `n.text` writes one.

A `meta.Convert<T, U>` gives `get(self, value: T) -> U` and `make(self, u: U) -> T`:

- `Float`'s `get` is exact for an `f32`, and its `make` rounds to `f32` as [numbers.conversions](06-numbers.md#numbers.conversions) does;
- a set's `make` keeps the first of equal elements, by the element type's own `Eq` and `Hash`;
- a map's `make` keeps the last value of equal keys, at the position of the first, by the key type's own `Eq` and `Hash`.

A map's default is no part of its shape, so a map that `make` gives has none. A `meta.Sized<T, E>` gives `get(self, value: T) -> List<E>`, `make(self, xs: List<E>) -> Option<T>` and `len(self) -> i64`. Its `make` is `None` unless `xs` has `n` elements.

Tests: [reflection/shapes_collections.lt](../conformance/reflection/shapes_collections.lt), [reflection/shapes_integers.lt](../conformance/reflection/shapes_integers.lt), [reflection/shapes_map_default.lt](../conformance/reflection/shapes_map_default.lt), [reflection/shapes_scalars.lt](../conformance/reflection/shapes_scalars.lt).

<a id="meta.private-fields"></a>
A shape gives every field of its type and every variant, whatever their visibility ([program.visibility](04-programs.md#program.visibility)).

Tests: [reflection/visibility/main.lt](../conformance/reflection/visibility/main.lt).

<a id="meta.accessor-effects"></a>
Every accessor of `std.meta` performs nothing and never panics. `n.parse`, `Array`'s `make` and every other `make` allocate where the type they make does ([facts.allocation](15-facts.md#facts.allocation)).

Tests: [reflection/shapes_integers.lt](../conformance/reflection/shapes_integers.lt).

## Fresh types, fields and cases

<a id="meta.fresh-types"></a>
`E`, `K` and `V` of [meta.shapes](#meta.shapes) are **fresh types**. In the arm of a `match` whose pattern names the case, each is a rigid type ([polymorphism.rigid-types](07-types.md#polymorphism.rigid-types)) of its own, distinct from every other and with no bound. The arm's code can give a fresh type to a function that takes a type parameter, but can't name it. No arm refines `T` itself: in an `Int` arm, `T` is still the type parameter, and the arm reads `value` through its accessor. A fresh type has no bound, so `x == y` on two values of one is E0318, *unsatisfied bound*, as it is for any type parameter without `Eq` ([traits.unsatisfied-bounds](11-traits.md#traits.unsatisfied-bounds)).

Tests: [reflection/fresh_errors.lt](../conformance/reflection/fresh_errors.lt), [reflection/fresh_types.lt](../conformance/reflection/fresh_types.lt), [reflection/shapes_collections.lt](../conformance/reflection/shapes_collections.lt).

<a id="meta.leaving-arm"></a>
A value whose type contains a fresh type can't leave its arm. Each of these, when its type contains a fresh type, is E0351, *value of a fresh type leaving its arm*, at the expression:

- an arm's value;
- a value assigned or passed `inout` to a variable declared outside the arm;
- a value returned or raised, even where a `try` in the arm catches it;
- any expression whose type would decide a type that inference left open outside the arm, as `acc.push(x)` does for a `var acc = []` declared before the arm.

Against a type already known outside the arm, as an arm's value where `str` is expected, a fresh type is E0311, *mismatched types* ([types.mismatch](07-types.md#types.mismatch)). It is E0311 too against the type of a literal declared outside, as `var n = 1`, which only a number type can be ([numbers.literal-defaults](06-numbers.md#numbers.literal-defaults)).

Tests: [reflection/fresh_against_known_types.lt](../conformance/reflection/fresh_against_known_types.lt), [reflection/fresh_errors.lt](../conformance/reflection/fresh_errors.lt).

<a id="meta.fields"></a>
A `meta.Fields<T>` is iterated by `for` and `comptime for`, which bind each field, in order, to a value of type `meta.Field<T, F>`. `F` is a fresh type of the loop's body, as it would be of an arm. So a variable declared in the arm around the loop is outside the body. A field gives `name(self) -> str`, `index(self) -> i64`, counted from 0, and `get(self, value: T) -> F`, the field's value. `fields.len()` is the number of fields.

Tests: [reflection/fresh_against_known_types.lt](../conformance/reflection/fresh_against_known_types.lt), [reflection/fresh_errors.lt](../conformance/reflection/fresh_errors.lt), [reflection/fresh_types.lt](../conformance/reflection/fresh_types.lt), [reflection/shapes_fields.lt](../conformance/reflection/shapes_fields.lt).

<a id="meta.building"></a>
`fields.build(f)`, for `f: fn<F>(meta.Field<T, F>) -> F`, makes a `T` from the value that `f` gives each field. It calls `f` once on each field, in order, and on no field after one of its calls raises. `f`'s effects pass through to the caller ([polymorphism.effects-and-escaping](07-types.md#polymorphism.effects-and-escaping)). `f` is given as any polymorphic argument is ([polymorphism.arguments](07-types.md#polymorphism.arguments)): a generic function, a closure literal or a parameter passed on. So a closure bound to a local first is E0311, *mismatched types*.

Tests: [reflection/build.lt](../conformance/reflection/build.lt), [reflection/build_errors.lt](../conformance/reflection/build_errors.lt).

<a id="meta.variant-cases"></a>
A `meta.Cases<T>` is iterated by `for` and `comptime for` in the order of the variants' declaration. Each case is a `meta.Case<T, P>`, where `P` is a fresh type of the loop's body. `P` is the tuple of the variant's payload fields: `()` for a variant without one, and a one-element tuple for one field. A case gives `name(self) -> str`, `index(self) -> i64`, `get(self, value: T) -> Option<P>` and `make(self, payload: P) -> T`. Its `get` is `Some` of the payload when `value` is that variant, and `None` otherwise. `cases.len()` is the number of cases.

Tests: [reflection/fresh_types.lt](../conformance/reflection/fresh_types.lt), [reflection/shapes_cases.lt](../conformance/reflection/shapes_cases.lt).

## What reflects

<a id="meta.reflects"></a>
A function **reflects** on a type parameter `T` when its body names `T.shape()`, or gives `T` to a type parameter of a function that reflects on it. It reflects **on the parts** of `T` when it gives a fresh type of `T`'s shape to a function that reflects on it, directly or through another function's type parameter. The **guards** of a function that reflects on `T` are the traits that the bound tests on `T` name in the body that names `T.shape()` ([meta.bound-tests](#meta.bound-tests)). `ToJson`, for example, guards `std.json`'s writers.

`reflects T` is an inferred fact, as implicit effects are ([facts.implicit-effects](15-facts.md#facts.implicit-effects)). No bound declares it, and `stilt show` prints it beside the function's signature. No `without` names it, and it is no part of a package's API ([versions.facts-in-api](21-versions.md#versions.facts-in-api)).

Tests: [reflection/build.lt](../conformance/reflection/build.lt), [reflection/fresh_types.lt](../conformance/reflection/fresh_types.lt), [reflection/reflects_accepted.lt](../conformance/reflection/reflects_accepted.lt), [reflection/reflects_errors.lt](../conformance/reflection/reflects_errors.lt).

<a id="meta.types-without-shape"></a>
A function type, a handler type, and a native type of `std` to which [meta.shapes](#meta.shapes) gives no case have no shape. `View`, `Iter`, `Lazy`, `Shared`, `Task` and `Scope` are among those native types.

A function that reflects on `T` is instantiated by a call or by naming it as a value. There, the type given for `T` must have a shape, unless it has an impl of one of the function's guards. When the function reflects on the parts of `T`, each type that `T`'s fields, elements and payloads hold, at any depth, must have a shape too. These types are walked depth first in the order of [meta.shapes](#meta.shapes), each type once, skipping a type with an impl of a guard and what it holds.

The first type that fails is E0350, *type without a shape given to a function that reflects*. It is reported once, at the first argument whose type holds it, or at the call or the name when none does. Its message names that type, the types that hold it, and the chain of functions that reflect, from the one instantiated to the one that names `T.shape()`.

Tests: [json/reflection_errors.lt](../conformance/json/reflection_errors.lt), [reflection/reflects_accepted.lt](../conformance/reflection/reflects_accepted.lt), [reflection/reflects_errors.lt](../conformance/reflection/reflects_errors.lt).

<a id="meta.unseen-instantiations"></a>
A type given for a type parameter of the function in which the instantiation stands makes that function reflect ([meta.reflects](#meta.reflects)). So the error is reported where a type without a shape is first written. Where an instantiation can't be seen, E0350 is at the expression that reflects or instantiates. These instantiations can't be seen:

- a function that reflects, given for a polymorphic function type ([polymorphism.arguments](07-types.md#polymorphism.arguments));
- a function of a trait, or of an impl of one, that reflects on its own type parameters, or a trait's default method that reflects on `Self`, which callers reach through a bound.

In an impl for a type, `Self` is that type, which is seen. An impl's own type parameters are checked where a bound is met by the impl, as the impl's bounds are ([traits.bounds](11-traits.md#traits.bounds)).

Tests: [reflection/impl_params.lt](../conformance/reflection/impl_params.lt), [reflection/impl_of_an_unknown_trait.lt](../conformance/reflection/impl_of_an_unknown_trait.lt), [reflection/impl_params_errors.lt](../conformance/reflection/impl_params_errors.lt), [reflection/reflects_errors.lt](../conformance/reflection/reflects_errors.lt).

## Bound tests

<a id="meta.bound-tests"></a>
The condition of an `if` or of an `else if` may be a **bound test**, `T: B + …` ([syntax.bound-tests](03-syntax.md#syntax.bound-tests)), as in `if T: Show { … } else { … }`. `T` is a type parameter in scope, and each `B` is a bound as a generic writes it ([traits.bounds](11-traits.md#traits.bounds)). The test is true when the type that instantiates `T` has an impl of every trait it names, with the bound's arguments, whose own bounds hold as they are checked for a call. Inside the branch it guards, `T` has the bounds besides its own. So `value.show()` resolves there, and calls the type's impl, a structural one included.

The `else` branch knows nothing more, and a method of the bound called there is E0314, *no such method or member*. A bound test stands only as the whole condition, so `a && T: Show` is E0100, *syntax error*. A `T` that names something other than a type parameter in scope is E0212, *wrong kind of name*. A module that writes a bound test is in the meta tier ([meta.reflection-tier](#meta.reflection-tier)).

Tests: [reflection/bound_test_errors.lt](../conformance/reflection/bound_test_errors.lt), [reflection/bound_test_syntax.lt](../conformance/reflection/bound_test_syntax.lt), [reflection/bound_tests.lt](../conformance/reflection/bound_tests.lt), [reflection/reflects_accepted.lt](../conformance/reflection/reflects_accepted.lt), [reflection/shapes_collections.lt](../conformance/reflection/shapes_collections.lt).

<a id="meta.static-reflection"></a>
A bound test is static ([meta.static-expressions](#meta.static-expressions)). So are `T.shape()` and `T.name()`, and these accessors applied to static values: those that give a `meta.Fields` or a `meta.Cases`, a field's or a case's name and index, and `len()`. So `comptime match T.shape()` and `comptime for f in fields` are valid. A `comptime for` over the elements that a `List` arm gives is E0349, *staging annotation on a value known only at run time* ([meta.not-static](#meta.not-static)). Without `comptime`, `if T: Show` tests the bound at run time, so `comptime if T: Show` keeps the meaning of the program without its annotations ([meta.erasure](#meta.erasure)).

Tests: [reflection/bound_tests.lt](../conformance/reflection/bound_tests.lt), [reflection/static.lt](../conformance/reflection/static.lt), [reflection/static_errors.lt](../conformance/reflection/static_errors.lt).

<a id="meta.reflection-tier"></a>
A module that names `std.meta` or writes a bound test is in the meta tier ([program.module-tier](04-programs.md#program.module-tier)). A module that only calls a function that reflects, as `json.to_text(user)`, stays in its tier, as one that only uses a macro does ([macros.advanced-tier](#macros.advanced-tier)).

Tests: [reflection/bound_tests.lt](../conformance/reflection/bound_tests.lt), [reflection/tier/main.lt](../conformance/reflection/tier/main.lt).

## Procedural macros

<a id="macros.procedural-declarations"></a>
`macro name(p: T, …) -> R / row { body }` declares a **procedural macro** (the `macro` production, [syntax.macros](03-syntax.md#syntax.macros)). A procedural macro is an item with a `lower` name in the value namespace of functions, constants and pattern macros. It may be `pub` and take doc comments. Its declaration must keep these rules:

- Each parameter's type is one of `std.meta`'s input types: `meta.Expr`, `meta.Pattern`, `meta.Type`, `meta.Text`, `meta.File` or `meta.Tokens`. Only the last parameter may be `meta.Tokens`.
- `R` is `meta.Expr`, `meta.Pattern` or `meta.Type`.
- The row is empty or `raise<meta.Error>`.
- The macro has no generics and no `without` clause.

Anything else is E0228, *malformed macro declaration*, at the part that breaks the rule. Procedural macros belong to the meta tier ([macros.meta-tier](#macros.meta-tier)).

Tests: [procedural/declaration_errors.lt](../conformance/procedural/declaration_errors.lt), [procedural/forms/main.lt](../conformance/procedural/forms/main.lt), [procedural/part_words.lt](../conformance/procedural/part_words.lt).

<a id="macros.procedural-bodies"></a>
A procedural macro's body is checked as the body of a function of its signature. Compile-time code performs nothing:

- a call in it that performs `io`, directly or through the functions it calls, is E0502, *effect that doesn't fit the row*, there ([effects.inference](12-effects.md#effects.inference));
- a call that raises an error its row doesn't name is E0502 when the row is empty, and E0503, *two error types*, when it is `raise<meta.Error>` ([effects.one-error-type](12-effects.md#effects.one-error-type)).

Its implicit effects are allowed: it allocates, and a panic stops it ([macros.step-limits](#macros.step-limits)). Its body is not compared with other bodies for duplicates ([docs.bodies-compared](04-programs.md#docs.bodies-compared)).

Tests: [packages/granted_macro_run](../conformance/packages/granted_macro_run/), [procedural/bodies/main.lt](../conformance/procedural/bodies/main.lt), [procedural/copies.lt](../conformance/procedural/copies.lt), [procedural/declaration_errors.lt](../conformance/procedural/declaration_errors.lt), [procedural/effects/main.lt](../conformance/procedural/effects/main.lt), [procedural/numbers](../conformance/procedural/numbers/), [procedural/reaching_io/main.lt](../conformance/procedural/reaching_io/main.lt).

<a id="macros.meta-use"></a>
`meta use a.b` makes the procedural macros of the module `a.b` available as `b.name!`, and nothing else of it. `use a.b` makes its other items available, its pattern macros among them. A module may write both. `meta use` is an import, so a cycle through it is E0206, *import cycle* ([program.no-cycles](04-programs.md#program.no-cycles)). A procedural macro is used only through `meta use`. In its own module, `name!(…)`, in code or in a quote, is E0212, *wrong kind of name*, and so is its name without `!`.

Tests: [checking/broken_procedural_macro.lt](../conformance/checking/broken_procedural_macro.lt), [procedural/cycle/main.lt](../conformance/procedural/cycle/main.lt), [procedural/imports_both/main.lt](../conformance/procedural/imports_both/main.lt), [procedural/imports_meta_only/main.lt](../conformance/procedural/imports_meta_only/main.lt), [procedural/meta_use_begins_a_part.lt](../conformance/procedural/meta_use_begins_a_part.lt), [procedural/names.lt](../conformance/procedural/names.lt), [procedural/own_module.lt](../conformance/procedural/own_module.lt), [procedural/part_words.lt](../conformance/procedural/part_words.lt).

<a id="macros.quote"></a>
A **quote** is an expression that writes code (the `quote` production, [syntax.expressions](03-syntax.md#syntax.expressions)). It has four forms:

- `quote { … }`, of type `meta.Expr`, holds a block's statements, and its code is that block;
- `quote type { … }`, of type `meta.Type`, holds a type;
- `quote pattern { … }`, of type `meta.Pattern`, holds a pattern;
- `quote field { … }`, of type `meta.FieldInit`, holds one field of a record literal, `name: expr`.

`pattern` and `field` are words of the grammar only after `quote` ([lexical.contextual-keywords](02-lexical.md#lexical.contextual-keywords)). So every tool parses a quote without resolving names. Contents that don't parse as their form are E0100, *syntax error*, at the first token that doesn't fit. A quote may use pattern macros, and the procedural macros of the modules that its module names with `meta use`, which expand in the expansion. A module that writes a quote is in the meta tier ([macros.meta-tier](#macros.meta-tier)).

Tests: [procedural/forms/main.lt](../conformance/procedural/forms/main.lt), [procedural/names.lt](../conformance/procedural/names.lt), [procedural/quote_syntax.lt](../conformance/procedural/quote_syntax.lt).

<a id="macros.splices"></a>
In a quote, `$x` splices a binding of the macro's own code, and `$(e)` any expression of it ([syntax.quotes](03-syntax.md#syntax.quotes)). A splice stands where its value's form may stand: a `meta.Expr` as an expression, a `meta.Pattern` as a pattern and a `meta.Type` as a type. A `meta.Name` stands wherever a binding, a variable or a field is named ([macros.tokens-and-code](#macros.tokens-and-code)). Each splice stands as one form, as if parenthesized, as a pattern macro's fragment does ([macros.expansion](#macros.expansion)). A splice of a value of another type, or in another place, is E0311, *mismatched types*, at the splice. `$` stands only in quotes and in pattern macros' declarations ([macros.templates](#macros.templates)).

Tests: [procedural/forms/main.lt](../conformance/procedural/forms/main.lt), [procedural/quote_errors.lt](../conformance/procedural/quote_errors.lt), [procedural/quote_syntax.lt](../conformance/procedural/quote_syntax.lt), [procedural/splices/main.lt](../conformance/procedural/splices/main.lt).

<a id="macros.literal-splices"></a>
A spliced value of type `str`, of an integer type, `bool` or a float type stands as a literal of its value. A `str` is written with `\` and `"` escaped, and `{` written `\{`, so it never interpolates. An integer is written as its decimal digits, and a float as [numbers.printing-floats](06-numbers.md#numbers.printing-floats) prints it. Each is written without a type, and inference types it where it lands ([numbers.literal-defaults](06-numbers.md#numbers.literal-defaults)). A negative number is written in parentheses, as `(-3)`, with its `-` part of the literal ([numbers.negative-literals](06-numbers.md#numbers.negative-literals)). So the least value of a type fits where it lands. A NaN or an infinite float stops the macro, as a panic does ([macros.step-limits](#macros.step-limits)).

Tests: [procedural/limits/main.lt](../conformance/procedural/limits/main.lt), [procedural/negative_splices/main.lt](../conformance/procedural/negative_splices/main.lt), [procedural/splices/main.lt](../conformance/procedural/splices/main.lt).

<a id="macros.spreads"></a>
`$..x` and `$..(e)` spread a `List` of values that may be spliced among the elements of a list, the elements of a tuple or the arguments of a call. They spread a `List<meta.FieldInit>` among a record literal's fields. In a quote, a `{` followed by a spread, or by a splice and a `:`, begins a record literal, never a block ([syntax.quotes](03-syntax.md#syntax.quotes)). A spread of anything else, and a list spliced without `..`, as `[$xs]` for `xs: List<i64>`, are E0311, *mismatched types*.

Tests: [procedural/quote_errors.lt](../conformance/procedural/quote_errors.lt), [procedural/splices/main.lt](../conformance/procedural/splices/main.lt).

<a id="macros.quote-hygiene"></a>
A quote's names are resolved where the quote is written, when its module is checked. So its hygiene is lexical, and nothing breaks it. A name that the quote binds, by `let`, `var`, a pattern, a closure's parameter or a `for`, is fresh in each expansion. No name the user wrote refers to it, and it hides none of the user's. Any other name that the quote writes resolves among the items and imports of the macro's module, private ones included. A name that names nothing there is E0211, *unknown name*, at the name. This includes a local of the macro's own code, as `n` after `let n = 3`, whose fix writes `$n`. A spliced `meta.Name` resolves as its kind says ([macros.tokens-and-code](#macros.tokens-and-code)).

Tests: [procedural/hygiene/main.lt](../conformance/procedural/hygiene/main.lt), [procedural/quote_errors.lt](../conformance/procedural/quote_errors.lt).

<a id="macros.linking"></a>
An expansion that names an item of the macro's module or of its imports makes that item part of the program, as if the using module had named it. Nothing else of the macro's module is part of the program.

Tests: [procedural/hygiene/main.lt](../conformance/procedural/hygiene/main.lt), [procedural/splices/main.lt](../conformance/procedural/splices/main.lt).

<a id="macros.procedural-uses"></a>
A use of a procedural macro is written as a pattern macro's ([macros.uses](#macros.uses)), `path!( … )` or `path![ … ]` with an optional trailing block. It stands where an expression or a pattern may, as its result's form says. A use of a macro whose result is `meta.Type` stands where a type may ([syntax.macro-uses](03-syntax.md#syntax.macro-uses)). A use anywhere else is E0223, *macro out of place*.

Tests: [procedural/forms/main.lt](../conformance/procedural/forms/main.lt), [procedural/use_errors/main.lt](../conformance/procedural/use_errors/main.lt).

<a id="macros.parts"></a>
A use's group is split into **parts** at its commas outside nested groups. An empty group has no parts, and one trailing comma is ignored. An empty part, as in `m!(a,,b)`, is E0227, *use whose parts don't fit its macro*, at its second comma. With a trailing block, the last parameter takes the block's contents, without its braces, and the group's parts go to the other parameters in order. Without one, the parts go to the parameters in order. A `meta.Tokens` last parameter then takes every part from its own on, with the commas between them, which may be no part at all. A part too many is E0227 at the part, and a part too few is E0227 at the group's closing bracket.

Tests: [procedural/empty_tokens/main.lt](../conformance/procedural/empty_tokens/main.lt), [procedural/forms/main.lt](../conformance/procedural/forms/main.lt), [procedural/use_errors/main.lt](../conformance/procedural/use_errors/main.lt), [procedural/uses/main.lt](../conformance/procedural/uses/main.lt).

<a id="macros.part-forms"></a>
A `meta.Expr`, `meta.Pattern` or `meta.Type` parameter takes a part that parses whole as that form, or the use is E0227 at the part's first token that doesn't fit. A `meta.Text` or `meta.File` parameter takes a string literal without interpolation, or the use is E0227 at the part. The parsers that read a macro's input insert no terminator at the top level of the tokens they read, as inside `( … )` ([lexical.inside-brackets](02-lexical.md#lexical.inside-brackets)). They insert terminators again inside a `{ … }` group among those tokens. So `m!(a` and a newline before `+ b)` read `a + b`, and so do a trailing block's contents.

Tests: [procedural/newlines/main.lt](../conformance/procedural/newlines/main.lt), [procedural/use_errors/main.lt](../conformance/procedural/use_errors/main.lt), [procedural/uses/main.lt](../conformance/procedural/uses/main.lt).

<a id="macros.expansion-order"></a>
A use expands when the module that holds it is checked, after the macro's module and the modules it imports are checked. A macro whose module has an error expands no use and reports nothing there: each use stands as a failed use ([macros.failed-uses](#macros.failed-uses)).

Tests: [checking/broken_procedural_macro.lt](../conformance/checking/broken_procedural_macro.lt), [procedural/broken/main.lt](../conformance/procedural/broken/main.lt), [procedural/broken_macro/main.lt](../conformance/procedural/broken_macro/main.lt), [procedural/broken_part/main.lt](../conformance/procedural/broken_part/main.lt).

<a id="macros.tokens-and-code"></a>
`std.meta` declares the values that a procedural macro reads and writes, written in Stilt where the table doesn't say native:

| Item | What it is |
| --- | --- |
| `Span` (native) | A place in the user's source, or in a file that a use names; `a.to(b)` spans from `a`'s start to `b`'s end |
| `Token` (native) | A token as the lexer reads it ([lexical.tokens](02-lexical.md#lexical.tokens)), made only from a use's parts and by `Text.lex`: `kind(self) -> Kind`; `span(self) -> Span`, which keeps the token's line, which the parsers read to insert terminators inside a `{ … }` group ([macros.part-forms](#macros.part-forms)); and `name(self) -> Option<Name>`, the token as a name when it is an identifier |
| `Kind = \| Word(str) \| Number(str) \| Text(Text) \| Interpolated \| Punct(str) \| Group(Delim, Tokens)`, `Delim = \| Paren \| Bracket \| Brace` | What a token is: a word, which is an identifier or a keyword; a number or a punctuation mark, as written; a string literal, or `Interpolated` when it interpolates, which only a cursor's `expr` reads; or a group, whose tokens nest. Doc comments are left out |
| `Tokens = { items: List<Token>, close: Span }` | The tokens of a part, a group or a file, and the span of what ends them |
| `Text` (native) | A string literal or a file's text: `value(self) -> str`, decoded; `span(self, start: i64, end: i64) -> Span`, the source of the value's bytes from `start` to `end`, widened to whole escapes; and `lex(self) -> Tokens / raise<Error>`, its tokens, raising at the first character that the lexer can't read |
| `File = { path: str, text: Text, span: Span }` | A file that a use names ([macros.named-files](#macros.named-files)), its path as written, and the span of the literal |
| `Name` (native) | An identifier, with `text(self) -> str` and `span(self) -> Span`, made only by `Token.name` and by `fresh(text: str) -> Name`. A name from a token is the user's: spliced as a binding, it binds that name where the use is, and as a variable it resolves there. A name from `fresh` is new at each call and distinct from every other, its text `text` and its span the use's: spliced as a binding and as variables, it binds and names one fresh name of the expansion |
| `Expr`, `Pattern`, `Type`, `FieldInit` (native) | Code, spliced and never taken apart; `span(self) -> Span`, which is the use's for code that a quote wrote |
| `Error` (native) | A diagnostic: `error(span: Span, message: str) -> Error`, and `note(self, span: Span, message: str) -> Error`, which keeps the first three notes |
| `Cursor` | A reader of tokens ([macros.cursor](#macros.cursor)) |

A macro makes a token or a name only through these functions, so the only names it writes that the user didn't write are fresh ones.

Tests: [procedural/errors/main.lt](../conformance/procedural/errors/main.lt), [procedural/files/main.lt](../conformance/procedural/files/main.lt), [procedural/forms/main.lt](../conformance/procedural/forms/main.lt), [procedural/hygiene/main.lt](../conformance/procedural/hygiene/main.lt), [procedural/outside_run.lt](../conformance/procedural/outside_run.lt), [procedural/splices/main.lt](../conformance/procedural/splices/main.lt).

<a id="macros.cursor"></a>
`meta.cursor(ts)` gives a `Cursor` at the first of the tokens `ts`. Its methods read the tokens in order: `peek`, `next`, `at_end`, `end`, `word`, `word_if`, `punct`, `punct_if`, `punct_of`, `name`, `names_by`, `text`, `number`, `group`, `expr`, `pattern`, `type_` and `braced_expr`. A method that expects something raises a `meta.Error` at the token it found, or at the closing span when none is left. The error's message says what the method expected and what it found. `word` compares ASCII letters without case.

`expr`, `pattern` and `type_` parse with the language's own parser and no terminator at the top level ([macros.part-forms](#macros.part-forms)). Each parses the longest prefix of the cursor's tokens that is a whole expression, pattern or type and stops before a `,`, a `;` or the end. `braced_expr` parses a `{ … }` group's contents as one expression. What they make from a use's tokens resolves where the use is. Every function of `std.meta` performs nothing.

Tests: [procedural/errors/main.lt](../conformance/procedural/errors/main.lt), [procedural/newlines/main.lt](../conformance/procedural/newlines/main.lt), [procedural/uses/main.lt](../conformance/procedural/uses/main.lt).

<a id="macros.named-files"></a>
A `meta.File` part's value is a path relative to a directory. The directory is that of the manifest of the package whose source holds the literal, or that of the program's root file when there is no manifest. The path must keep these rules:

- its names are separated by `/`, and none of them is empty, `.` or `..`, or starts with `.`;
- each name matches an entry of its directory byte for byte;
- it names a regular file whose real path lies inside the directory it is relative to, and whose contents are UTF-8.

Any other path is E0229, *file that a macro can't be given*, at the literal. The compiler reads the file, and a macro reads nothing itself. The file is an input of the program: an edit of it expands again the uses that name it.

Tests: [procedural/errors/main.lt](../conformance/procedural/errors/main.lt), [procedural/file_errors/main.lt](../conformance/procedural/file_errors/main.lt), [procedural/files/main.lt](../conformance/procedural/files/main.lt), [procedural/forms/main.lt](../conformance/procedural/forms/main.lt).

Checked by: also the toolchain's tests of named files, a link inside the package to a file outside it (`compiler/stilt-cli/tests/macros.rs`).

<a id="macros.running"></a>
A procedural macro's body runs once per use, given its parts. Its result replaces the use, which is then resolved and checked as code written there ([macros.expansion](#macros.expansion)). A macro sees only its parts and the files they name. So the same parts and files give the same expansion, and the order in which uses expand is not observable.

Tests: [procedural/bodies/main.lt](../conformance/procedural/bodies/main.lt), [procedural/forms/main.lt](../conformance/procedural/forms/main.lt), [procedural/hygiene/main.lt](../conformance/procedural/hygiene/main.lt), [procedural/natives_both_ways/main.lt](../conformance/procedural/natives_both_ways/main.lt), [procedural/numbers](../conformance/procedural/numbers/), [procedural/splices/main.lt](../conformance/procedural/splices/main.lt).

<a id="macros.raised-errors"></a>
A macro that raises `e` gives one diagnostic, E0225, *error raised by a macro*, at `e`'s span. It carries `e`'s message and notes, and a note that names the macro. A span in a named file places the diagnostic at the literal that names the file, with a note that gives the file's line and column.

Tests: [procedural/errors/main.lt](../conformance/procedural/errors/main.lt), [procedural/file_errors/main.lt](../conformance/procedural/file_errors/main.lt).

<a id="macros.failed-uses"></a>
A use whose macro raises, doesn't finish ([macros.step-limits](#macros.step-limits)), or has an error in its module ([macros.expansion-order](#macros.expansion-order)) stands as a **failed use**. No other diagnostic follows from a failed use. In an expression or a type, a failed use has the error type ([errors.error-type](18-errors.md#errors.error-type)). In a pattern, it matches every value and binds nothing. In the scope that a failed pattern opens, a name that names nothing has the error type and is reported nowhere ([program.programs-with-errors](04-programs.md#program.programs-with-errors)), and a literal whose expected type is the error type is not range-checked.

Tests: [procedural/broken/main.lt](../conformance/procedural/broken/main.lt), [procedural/errors/main.lt](../conformance/procedural/errors/main.lt), [procedural/use_errors/main.lt](../conformance/procedural/use_errors/main.lt).

<a id="macros.step-limits"></a>
A macro's run is counted in steps:

- one for the macro's own body, and one for each call of a function, a method or a closure whose body is written in Stilt, the standard library's included;
- one for each call of a native;
- one for each iteration of a loop.

A run stops when it does one of these:

- takes more than 10,000,000 steps;
- calls deeper than 10,000 frames, the macro's own body the first of them;
- runs out of memory;
- panics;
- reaches C, through a foreign function, `with_ptr`, `with_mut_ptr`, `with_c_str` or a native of `std.c` ([c.calls](20-builds.md#c.calls)).

A run that stops is E0226, *macro that didn't finish*, at the use. Its message names the reason, as a panic's kind and detail or the function through which the run reached C. It also names the frames of the macro's module's own functions that were running, innermost last. The use stands as a failed use ([macros.failed-uses](#macros.failed-uses)).

Tests: [foreign/compile_time/main.lt](../conformance/foreign/compile_time/main.lt), [procedural/all_steps/main.lt](../conformance/procedural/all_steps/main.lt), [procedural/limits/main.lt](../conformance/procedural/limits/main.lt), [procedural/memory/main.lt](../conformance/procedural/memory/main.lt), [procedural/one_step_more/main.lt](../conformance/procedural/one_step_more/main.lt), [procedural/reaching_io/main.lt](../conformance/procedural/reaching_io/main.lt).

Checked by: also the toolchain's tests of a run's memory, which every value it holds and the thread of each fiber count toward (`compiler/stilt-meta/src/value/weight.rs`, `compiler/stilt-meta/src/tests/limits.rs`).

<a id="macros.outside-run"></a>
A macro runs only while its uses expand. The functions it calls are ordinary functions, which a program may also call when it runs. In such a run:

- a quote evaluates its splices from left to right and makes its code, whatever their values;
- `fresh` makes a name;
- the span of what either makes is the place of the quote or of the call.

No observable of the run shows these values but a name's `text()`. Nothing else of [macros.tokens-and-code](#macros.tokens-and-code) can be made outside a macro's run.

Tests: [procedural/outside_run.lt](../conformance/procedural/outside_run.lt), [procedural/splices_outside_run.lt](../conformance/procedural/splices_outside_run.lt).

<a id="macros.meta-tier"></a>
A module that declares a procedural macro or writes a quote is in the meta tier ([program.module-tier](04-programs.md#program.module-tier)). A module that only uses a procedural macro stays in its tier, whatever the expansion writes.

Tests: [procedural/tier/main.lt](../conformance/procedural/tier/main.lt).

## Expansions

<a id="macros.nested-expansions"></a>
A template or a quote may use macros, its own macro among them, and each use in an expansion is expanded in turn. A use expanded inside 128 nested expansions, of pattern and procedural macros together, is E0224, *expansion too deep*, at the use that the user wrote. Its message names the chain of macros.

Tests: [macros/exponential.lt](../conformance/macros/exponential.lt), [macros/expressions.lt](../conformance/macros/expressions.lt), [macros/use_errors.lt](../conformance/macros/use_errors.lt), [procedural/limits/main.lt](../conformance/procedural/limits/main.lt).

<a id="macros.expansion-size"></a>
The expansions that a use the user wrote leads to hold at most 100,000 tokens in all. They are the use's own expansion and every expansion nested in it, of pattern and procedural macros together. Each counts the tokens of the code it gives: a pattern macro's template with its fragments substituted, or a procedural macro's result. An expansion that takes the count past 100,000 is E0231, *expansion too large*, at the use that the user wrote. Its message names the macro that gave it. After an expansion too large, or too deep ([macros.nested-expansions](#macros.nested-expansions)), nothing more of that use's expansions is resolved or reported, and the use has no expansion.

Tests: [macros/expansion_size.lt](../conformance/macros/expansion_size.lt), [macros/exponential.lt](../conformance/macros/exponential.lt), [procedural/expansion_size/main.lt](../conformance/procedural/expansion_size/main.lt).

<a id="macros.errors-in-expansions"></a>
A diagnostic in expanded code is reported at the tokens the user wrote:

- at a fragment's tokens, when it lies in them;
- at the tokens of a part that a spliced `meta.Expr`, `meta.Pattern`, `meta.Type` or `meta.Name` holds, when it lies in them;
- otherwise at the use, with a note that names the macro and shows the line of its template or quote.

Each token that a template or a quote writes is placed at the start of the use's path, the parentheses around a fragment included. Each token of a fragment or a part is placed where the user wrote it. An expansion inside an expansion is placed at the outermost use. One diagnostic is reported once, at one place, and the conformance tests compare these positions ([conformance.inline-annotations](01-conformance.md#conformance.inline-annotations)).

Tests: [macros/expansion_size.lt](../conformance/macros/expansion_size.lt), [macros/use_errors.lt](../conformance/macros/use_errors.lt), [procedural/errors/main.lt](../conformance/procedural/errors/main.lt).

<a id="macros.expansion-effects"></a>
Expanded code is the using function's code. Its effects, implicit effects and facts are inferred there ([effects.inference](12-effects.md#effects.inference), [facts.inference](15-facts.md#facts.inference)), and the function's `without` limits them. The capabilities that an expansion's own tokens name are the declaring package's, as a call into that package would be. A dependency's template or quote that names a native its grant doesn't cover is E0608, *effect that the manifest doesn't grant*, at the dependency's entry in the manifest. The dependency's own functions are reported the same way ([facts.ungranted-capabilities](15-facts.md#facts.ungranted-capabilities)).

Tests: [macros/ungranted/main.lt](../conformance/macros/ungranted/main.lt), [macros/use_errors.lt](../conformance/macros/use_errors.lt), [packages/ungranted_macro_run](../conformance/packages/ungranted_macro_run/), [packages/ungranted_quote](../conformance/packages/ungranted_quote/), [procedural/effects/main.lt](../conformance/procedural/effects/main.lt).

<a id="macros.showing"></a>
`stilt show` prints a function with its macro uses as written. With `--expanded`, it prints each use's expansion in its place, with the lines that each expansion takes. A fresh name is printed as its text followed by `#` and a number, as `tmp#1`, which no program can write. The numbers follow the order in which the fresh names' bindings appear in the expansion. The language server expands every use and shows its expansion on hover. A failed use stays as written, and completion inside its groups proceeds as in an expression of the use's scope. A path-and-hash address ([edits.hash](19-tools.md#edits.hash)) names a use's tokens, never its expansion.

Checked by: the toolchain's tests of `show` (`compiler/stilt-cli/tests/macros.rs`) and of the language server (`compiler/stilt-cli/tests/lsp_macros.rs`).

<a id="macros.formatting"></a>
`stilt fmt` formats a pattern macro's patterns and templates token by token, a procedural macro as a function, and a quote's contents as the form they hold. It leaves the tokens of a use's groups as written, but for their indentation.

Checked by: the formatter's pairs `tests/format/macro_declarations`, `tests/format/macro_uses` and `tests/format/procedural_macros`, which `just formatter` checks.
