# 10. Declarations

A module's items include its record and variant types, its functions and its constants, and the name of each stands in one of the module's two namespaces. Besides the declared types, a program writes the built-in tuple, unit, `Never` and function types, and typed holes for code not yet written. Modules and visibility are defined in [Programs](04-programs.md), `impl` blocks and bounds in [Traits and methods](11-traits.md), and the generic forms of the advanced and meta tiers in [Types and generics](07-types.md).

## Record types

<a id="declarations.records"></a>
`type Name = { field: T, … }` declares a **record type**. A record type is nominal: two records with the same fields are different types. A value of one where the other is expected is E0311, *mismatched types*. A record may have no fields, and its list of fields may end with a comma. Anonymous record types and record bounds, which are structural, belong to the advanced tier ([records.anonymous-types](07-types.md#records.anonymous-types), [records.record-bounds](07-types.md#records.record-bounds)).

Tests: [declarations/distinct_records.lt](../conformance/declarations/distinct_records.lt), [declarations/records.lt](../conformance/declarations/records.lt), [expressions/trailing_commas.lt](../conformance/expressions/trailing_commas.lt), [ported/knapsack.lt](../conformance/ported/knapsack.lt).

## Variant types

<a id="declarations.variant-types"></a>
`type Name = | V₁(T, …) | V₂ | …` declares a **variant type**, each of whose values is exactly one of its variants. The `|` before the first variant is optional when there are two or more variants, and required when there is one, as in `type UserId = | UserId(i64)`. A variant written with parentheses has at least one payload field, so `type Signal = | Ping() | Pong` is E0100, *syntax error*. Payload fields are positional. A payload field may carry a name, as in `Circle(radius: f64)`, which documents it and appears in no pattern and no constructor.

Tests: [declarations/empty_payload.lt](../conformance/declarations/empty_payload.lt), [declarations/single_variant_without_bar.lt](../conformance/declarations/single_variant_without_bar.lt), [declarations/variants.lt](../conformance/declarations/variants.lt), [expressions/trailing_commas.lt](../conformance/expressions/trailing_commas.lt), [ported/balanced_brackets.lt](../conformance/ported/balanced_brackets.lt).

<a id="declarations.constructors"></a>
A variant with a payload is a function from its payload fields to its type, so `Circle` can be passed wherever an `fn(f64) -> Shape` is expected. A call of it must give one argument for each payload field, or it is E0315, *wrong number of arguments*. A variant without a payload is a value of its type. So `None()` and `Dot()` call what isn't a function, and are E0311, *mismatched types*.

Tests: [declarations/constructors.lt](../conformance/declarations/constructors.lt), [declarations/newtype.lt](../conformance/declarations/newtype.lt), [declarations/variants.lt](../conformance/declarations/variants.lt), [types/argument_counts.lt](../conformance/types/argument_counts.lt), [types/payloads.lt](../conformance/types/payloads.lt).

<a id="declarations.recursive-types"></a>
A type may contain itself, directly or through other types, and needs no box. A record must not contain itself through record fields and tuple elements alone, with no variant type, collection or function type in between. Declaring one is E0309, *record that contains itself*. Each group of records that contain one another this way is one error, at the last of their declarations. So `type Link = { value: i64, next: Link }` is E0309, while `next: Option<Link>` or `next: List<Link>` is valid.

Tests: [declarations/duplicate_cycles.lt](../conformance/declarations/duplicate_cycles.lt), [declarations/record_contains_itself.lt](../conformance/declarations/record_contains_itself.lt), [declarations/recursive_types.lt](../conformance/declarations/recursive_types.lt), [declarations/variants.lt](../conformance/declarations/variants.lt).

<a id="declarations.no-aliases"></a>
There are no type aliases. A `type X = …` whose right side is neither a record nor a variant type is E0100, *syntax error*. `type Ids = List<i64>`, `type Id = UserId` and `type Callback = fn(i64) -> i64` are each E0100. So is a single variant written without its `|`, as `type UserId = UserId(i64)`, which reads as an alias. A new nominal type over an existing one is a single variant, `type UserId = | UserId(i64)`, whose variant shares its type's name ([declarations.namespaces](#declarations.namespaces)).

Tests: [declarations/alias_forms](../conformance/declarations/alias_forms/), [declarations/newtype.lt](../conformance/declarations/newtype.lt), [declarations/single_variant_without_bar.lt](../conformance/declarations/single_variant_without_bar.lt).

## Type parameters and arguments

<a id="declarations.type-parameters"></a>
A record or variant type may take type parameters, `type Name<A, …> = …`. They are uppercase names and take no bounds, so `type Sorted<T: Ord> = …` is E0100, *syntax error*. Bounds are written on functions and impls ([traits.bounds](11-traits.md#traits.bounds)). A lowercase name without a type there is a row variable, which no type declares, so `type Task<e> = …` and `type Box<t> = …` are E0100 too ([effects.row-variables](12-effects.md#effects.row-variables)). A type's parameters may also hold value parameters ([generics.value-parameters](07-types.md#generics.value-parameters)) and, last, one pack ([variadics.packs](07-types.md#variadics.packs)).

Tests: [declarations/bound_on_type.lt](../conformance/declarations/bound_on_type.lt), [declarations/row_variable_on_type.lt](../conformance/declarations/row_variable_on_type.lt), [declarations/type_parameter_case.lt](../conformance/declarations/type_parameter_case.lt).

<a id="declarations.generic-lists"></a>
A list of generics or of type parameters, written `<…>`, holds at least one, as the grammar says ([syntax.generic-lists](03-syntax.md#syntax.generic-lists)). So `fn f<>()`, `type P<> = …` and `impl<> P` are E0100, *syntax error*.

Tests: [declarations/empty_function_generics.lt](../conformance/declarations/empty_function_generics.lt), [declarations/empty_impl_generics.lt](../conformance/declarations/empty_impl_generics.lt), [declarations/empty_type_parameters.lt](../conformance/declarations/empty_type_parameters.lt).

<a id="declarations.type-arguments"></a>
Wherever a type is written, a generic type takes exactly as many type arguments as it has parameters, as in `List<i64>`. This holds for a record, a variant type and a built-in type such as `List`. Any other number is E0300, *wrong number of type arguments*: `List`, `Option<i64, str>` and `T<i64>` for a type parameter `T` are each E0300. A type parameter and `Self` take none, except in a constructor trait ([traits.constructor-traits](11-traits.md#traits.constructor-traits)) and for a constructor parameter ([traits.constructor-parameters](11-traits.md#traits.constructor-parameters)). A type with value parameters takes a value argument in the position of each ([generics.value-arguments](07-types.md#generics.value-arguments)).

Expressions and patterns name a generic type without its arguments, which inference gives ([types.no-type-arguments](07-types.md#types.no-type-arguments)), as in `Map.with_default(0.0)` and `Point { x: 1 }`.

Tests: [declarations/type_arguments_inferred.lt](../conformance/declarations/type_arguments_inferred.lt), [names/type_arguments.lt](../conformance/names/type_arguments.lt).

## Namespaces and names

<a id="declarations.namespaces"></a>
A module has two **namespaces**. The **type namespace** holds its types, traits and effects. The **value namespace** holds its variants, functions, constants, macros and the modules that its `use` declarations bind ([program.one-value-namespace](04-programs.md#program.one-value-namespace)). Each name is unique within its namespace. So two variants named `Red` in one module, even of different types, are E0208, *name defined twice*, and so are a type and a trait of one name.

A name may stand in both namespaces, so a variant may share its type's name, as `UserId` does in `type UserId = | UserId(i64)`. The prelude's items stand in the same two namespaces. So a module may declare a variant `Eq` beside the prelude's trait `Eq`, while a type `Option` of its own is E0209, *name of a prelude item* ([program.contents](04-programs.md#program.contents)).

Tests: [declarations/duplicate_cycles.lt](../conformance/declarations/duplicate_cycles.lt), [declarations/namespaces.lt](../conformance/declarations/namespaces.lt), [declarations/newtype.lt](../conformance/declarations/newtype.lt), [names/defined_twice.lt](../conformance/names/defined_twice.lt), [program/prelude_other_namespace.lt](../conformance/program/prelude_other_namespace.lt), [program/prelude_same_namespace.lt](../conformance/program/prelude_same_namespace.lt), [program/use_and_item_clash.lt](../conformance/program/use_and_item_clash.lt).

<a id="declarations.unique-names"></a>
Each place that declares names holds a name once. These are the places:

- a namespace of a module
- a list of generics
- the parameters of a function
- the fields of a record
- the operations of an effect
- the inherent members of a type ([traits.inherent-names](11-traits.md#traits.inherent-names))
- the tests of a module ([program.test-declarations](04-programs.md#program.test-declarations))
- the names that one pattern binds

A second declaration of a name there is E0208, *name defined twice*, at the later one. `type Order = { qty: i64, qty: i64 }`, `fn g(x: i64, x: i64)` and `let (a, a) = pair` are each E0208.

Tests: [names/defined_twice.lt](../conformance/names/defined_twice.lt).

<a id="declarations.name-lookup"></a>
Where a name is written decides the namespace it is read in. `Name {` names a record type. `Name(…)`, and a bare `Name` in an expression or a pattern, name a value. So with a record type `Point` and a variant `Point(i64)` of another type, `Point(2)` is the variant.

In `Name.member`, `Name` is looked up in the type namespace first, then in the value namespace. So `UserId.new(…)` calls an associated function of the type `UserId`. For a type and a constant both named `Origin`, `Origin.x` looks for a member `x` of the type. When the type has no member `x`, it is E0314, *no such method or member*.

Tests: [declarations/member_lookup_order.lt](../conformance/declarations/member_lookup_order.lt), [declarations/newtype.lt](../conformance/declarations/newtype.lt).

<a id="declarations.unknown-names"></a>
A name that resolves to nothing where it is used is E0211, *unknown name*, at the name. A name resolves to nothing when no binding in scope has it ([expressions.scope](08-expressions.md#expressions.scope)), and none of these has it in the namespace where it is read:

- the module's items
- the prelude's items
- the modules that `use` binds

So a variant of another module written bare in an expression, as `Circle(1.0)` after `use shapes`, is E0211 ([declarations.qualified-variants](#declarations.qualified-variants)). A body reports each unknown name once ([errors.unknown-names](18-errors.md#errors.unknown-names)).

Tests: [names/unqualified_variant](../conformance/names/unqualified_variant/), [patterns/bare_variant_errors](../conformance/patterns/bare_variant_errors/).

<a id="declarations.qualified-variants"></a>
Code in another module names a variant by its qualified name, as in `shapes.Circle(1.0)`. A pattern is the exception: it names a variant through the type it matches ([patterns.variants-by-type](09-patterns.md#patterns.variants-by-type)). The prelude's variants, such as `Some` and `Ok`, need no qualifier ([program.contents](04-programs.md#program.contents)).

Tests: [names/unqualified_variant](../conformance/names/unqualified_variant/), [patterns/bare_variants](../conformance/patterns/bare_variants/), [patterns/qualified_patterns](../conformance/patterns/qualified_patterns/), [program/visibility](../conformance/program/visibility/).

<a id="declarations.wrong-kind-of-name"></a>
A name that resolves to something of a kind that can't stand where it is written is E0212, *wrong kind of name*, at the name. So each of these is E0212:

- a record type used as a value, as `Point(1, 2)` or `Point` alone for a record type `Point`
- a module used as a value
- a trait used as a type
- a type named as a bound, as in `<T: Point>`
- a value parameter or a constant written where a type stands

Tests: [generics/value_parameter_as_a_type.lt](../conformance/generics/value_parameter_as_a_type.lt), [names/record_type_called.lt](../conformance/names/record_type_called.lt), [names/wrong_kind.lt](../conformance/names/wrong_kind.lt).

## Built-in types

<a id="declarations.tuples-and-unit"></a>
Tuple types are written `(A, B, …)`, and a one-element tuple type is written `(A,)`. A parenthesized `(A)` is `A`. The **unit type** `()` has exactly one value, also written `()`.

Tests: [declarations/unit_and_tuples.lt](../conformance/declarations/unit_and_tuples.lt).

<a id="declarations.never"></a>
`Never` has no values, and an expression of type `Never` converts to any type. These have type `Never`:

- `raise`, `return`, `break` and `continue`
- calls of `exit`, `panic` and `unreachable`
- a `loop` with no `break` that exits it ([expressions.loop-types](08-expressions.md#expressions.loop-types))

Tests: [declarations/never.lt](../conformance/declarations/never.lt), [expressions/if_never_branch.lt](../conformance/expressions/if_never_branch.lt), [expressions/loop_never.lt](../conformance/expressions/loop_never.lt), [expressions/loop_value_types.lt](../conformance/expressions/loop_value_types.lt), [records/anonymous_never.lt](../conformance/records/anonymous_never.lt), [types/loop_types.lt](../conformance/types/loop_types.lt), [types/never_converts.lt](../conformance/types/never_converts.lt).

## Function types

<a id="declarations.function-types"></a>
A function type is written `fn(A, B) -> C / row`, and when its return type is left out, it is `()`. A parameter's mode is part of the type, as in `fn(inout A)`. So a function value with an `inout` parameter takes an `inout` argument there ([expressions.inout-arguments](08-expressions.md#expressions.inout-arguments)). A function type may declare type parameters of its own, as in `fn<T: Show>(T) -> str` ([polymorphism.function-types](07-types.md#polymorphism.function-types)). A handler's type is written as its literal begins, `handler Name` or `handler Name -> R`, with a row ([handlers.handler-types](12-effects.md#handlers.handler-types)).

Tests: [expressions/closure_inout_in_list.lt](../conformance/expressions/closure_inout_in_list.lt), [expressions/closure_inout_parameters.lt](../conformance/expressions/closure_inout_parameters.lt), [expressions/inout_function_values.lt](../conformance/expressions/inout_function_values.lt).

<a id="declarations.function-type-rows"></a>
A row after a function type belongs to the innermost function type that has none yet. So in `fn make() -> fn(i64) -> i64 / io`, the row is part of the returned type, and `make` itself performs no effects. In `fn make() -> (fn(i64) -> i64) / io`, the parentheses hold the whole returned function type, and the row belongs to `make`.

Tests: [declarations/function_type_rows.lt](../conformance/declarations/function_type_rows.lt).

## Functions

<a id="declarations.function-declarations"></a>
A function declaration has this form, in which every part but the name, the parameters and the body may be left out:

```text
pub? extern? fn name<generics>(params) (-> T)? (/ row)? (where …)? (without limits)? (block | = ?)
```

Its generics are of four kinds:

- type parameters, uppercase names that may carry bounds, as `T: Ord + Show` ([traits.bounds](11-traits.md#traits.bounds))
- row variables, which are lowercase names ([effects.row-variables](12-effects.md#effects.row-variables))
- value parameters ([generics.value-parameters](07-types.md#generics.value-parameters))
- packs ([variadics.packs](07-types.md#variadics.packs))

When its return type is left out, it is `()`. A result written `inout T` makes the function a projection ([projections.declaring-projection](13-modes.md#projections.declaring-projection)). `= ?` gives it a body that is a single hole ([declarations.typed-holes](#declarations.typed-holes)).

`extern` after `pub`, on a module's function with a body, exports the function to C ([c.exported-functions](20-builds.md#c.exported-functions)). `extern` on a module's function without a body, `pub` or not, declares a foreign function, which C gives ([c.foreign-functions](20-builds.md#c.foreign-functions)).

Tests: [declarations/functions.lt](../conformance/declarations/functions.lt), [declarations/holes.lt](../conformance/declarations/holes.lt), [ported/ackermann.lt](../conformance/ported/ackermann.lt), [ported/gcd.lt](../conformance/ported/gcd.lt).

<a id="declarations.parameters"></a>
A parameter is written `mode? name: T`, where the mode is `inout` ([values.inout-arguments](05-values.md#values.inout-arguments)). A parameter without a mode is a `let` parameter. `let` is never written there, so `fn twice(let x: i64)` is E0100, *syntax error*. A default value, as in `name: str = "world"`, is E0100 too.

A parameter of function type that the function may keep is written `escaping name: fn(…)`, with no mode and a type written with `fn` ([effects.escaping-parameters](12-effects.md#effects.escaping-parameters)). So `escaping` is E0100 before a parameter of another type, after a mode, and before a parenthesized function type. A method's first parameter may be `self` or `inout self`, with no type, except in a constructor trait and its impls ([traits.methods](11-traits.md#traits.methods), [traits.receiver-types](11-traits.md#traits.receiver-types)).

Tests: [declarations/default_parameter.lt](../conformance/declarations/default_parameter.lt), [declarations/escaping_after_mode.lt](../conformance/declarations/escaping_after_mode.lt), [declarations/escaping_non_function.lt](../conformance/declarations/escaping_non_function.lt), [declarations/escaping_parenthesized.lt](../conformance/declarations/escaping_parenthesized.lt), [declarations/let_parameter.lt](../conformance/declarations/let_parameter.lt), [ported/hanoi.lt](../conformance/ported/hanoi.lt).

<a id="declarations.limits"></a>
`without L, …` after a function's signature limits the facts that the compiler infers about its body, including what the functions it names contribute ([Inferred facts and limits](15-facts.md)). Its limits are those that a module header takes ([program.module-header](04-programs.md#program.module-header)):

- `panic`, `overflow`, `alloc`, `div` and `copy`
- the capabilities `fs`, `net`, `clock`, `env`, `console`, `rand`, `spawn` and `exec`
- `locks` and `unsafe`

A limit named twice is E0202, *`without` given twice*, at its second occurrence. The clause may start on the line after the signature, which it continues ([lexical.continuation-lines](02-lexical.md#lexical.continuation-lines)). The clause isn't part of the function's signature. So a trait's function declared without a body takes none, and an impl's function may carry a clause that the trait's declaration doesn't.

Tests: [declarations/function_limits.lt](../conformance/declarations/function_limits.lt), [declarations/repeated_limit.lt](../conformance/declarations/repeated_limit.lt), [lexical/contextual_keywords.lt](../conformance/lexical/contextual_keywords.lt), [lexical/without_on_next_line.lt](../conformance/lexical/without_on_next_line.lt), [lexical/without_on_next_line_rejected.lt](../conformance/lexical/without_on_next_line_rejected.lt).

## Typed holes

<a id="declarations.typed-holes"></a>
`?` is a **typed hole**, or **hole**: an expression that stands for code not yet written. It may be a whole body, `= ?`, or stand inside one, as in `a + ?`. A hole takes the type its context expects. A hole whose type can't be inferred, as in `let x = ?`, is E0312, *type that can't be inferred* ([types.known-types](07-types.md#types.known-types)). Each hole is the warning W0300, *hole*, at the hole. `?` is always a hole, even directly before `.`, `..` or `..=` ([types.hole-before-dot](07-types.md#types.hole-before-dot)). It is never an operator, so `parse(s)?` is E0100, *syntax error*.

Tests: [checking/hole_called_with_a_broken_spread.lt](../conformance/checking/hole_called_with_a_broken_spread.lt), [declarations/hole_uninferred.lt](../conformance/declarations/hole_uninferred.lt), [declarations/holes.lt](../conformance/declarations/holes.lt), [expressions/if_let_hole.lt](../conformance/expressions/if_let_hole.lt), [expressions/question_mark_operator.lt](../conformance/expressions/question_mark_operator.lt), [lexical/bare_hole_before_range.lt](../conformance/lexical/bare_hole_before_range.lt), [lexical/hole_before_dot_rejected.lt](../conformance/lexical/hole_before_dot_rejected.lt), [lexical/hole_before_range.lt](../conformance/lexical/hole_before_range.lt), [lexical/hole_ends_line.lt](../conformance/lexical/hole_ends_line.lt), [protocol/comment_warnings_with_errors.lt](../conformance/protocol/comment_warnings_with_errors.lt), [variadics/hole_called_with_a_spread.lt](../conformance/variadics/hole_called_with_a_spread.lt).

<a id="declarations.running-holes"></a>
A program with holes still runs. Reaching a hole panics with the kind `hole` ([effects.panic-kinds](12-effects.md#effects.panic-kinds)), so a test that reaches one fails. A release build refuses a program that holds a hole ([builds.what-it-refuses](20-builds.md#builds.what-it-refuses)).

Tests: [declarations/hole_in_test.lt](../conformance/declarations/hole_in_test.lt), [declarations/hole_reached.lt](../conformance/declarations/hole_reached.lt), [effects/panic_hole.lt](../conformance/effects/panic_hole.lt), [program/run_with_warnings.lt](../conformance/program/run_with_warnings.lt), [projections/hole_arm.lt](../conformance/projections/hole_arm.lt).

<a id="declarations.native-items"></a>
In the standard library's sources, `?` marks what each implementation provides itself. These are the **native** items:

- the body of a native function
- the value of a native constant
- the representation of a native type, declared `pub type Name<…> = ?`, as `View<T>` is ([views.std-view](13-modes.md#views.std-view))

These uses of `?` are not holes: they get no warning, never panic, and are allowed in constants and in release builds. Only `std` declares native types.

Checked by: the standard library's sources in `std/`, which every implementation reads and checks with every program it checks.

## Constants

<a id="declarations.constant-declarations"></a>
`pub? const NAME: T = e` declares a constant. Its name must be uppercase ([lexical.case](02-lexical.md#lexical.case)) and its type annotation is required, so `const limit: i64 = 10` and `const LIMIT = 10` are E0100, *syntax error*. A constant may be declared in these places:

- at module level
- inside an inherent `impl` block, where it is read as `Type.NAME`, as `f64.PI` is ([traits.associated-functions](11-traits.md#traits.associated-functions))
- in a trait and its impls ([traits.trait-constants](11-traits.md#traits.trait-constants))

Tests: [declarations/const_lowercase.lt](../conformance/declarations/const_lowercase.lt), [declarations/const_without_type.lt](../conformance/declarations/const_without_type.lt), [declarations/constants](../conformance/declarations/constants/), [ported/roman_numerals.lt](../conformance/ported/roman_numerals.lt), [traits/inherent_methods.lt](../conformance/traits/inherent_methods.lt).

<a id="declarations.impl-constants"></a>
A constant of an inherent block has one value for every type argument of its block. In a block with type parameters, the constant's type can't name those parameters, which are not in scope there: naming one is E0211, *unknown name*. Nor can it name `Self`, which is E0215, *`self` or `Self` where it doesn't exist*. `Type.NAME` takes no type arguments: after `impl<T> Stack<T> { const LIMIT: i64 = 100 }`, `Stack.LIMIT` is valid.

Tests: [declarations/generic_impl_constant.lt](../conformance/declarations/generic_impl_constant.lt), [declarations/generic_impl_constant_type.lt](../conformance/declarations/generic_impl_constant_type.lt).

<a id="declarations.constant-evaluation"></a>
A constant is evaluated when the program first uses its value, and only then. Its value can panic only where a unary `-` overflows ([numbers.integer-panics](06-numbers.md#numbers.integer-panics)). That panic happens at the first use and is reported at the `-`, so a constant that the program never uses never panics.

Tests: [declarations/constant_in_loop.lt](../conformance/declarations/constant_in_loop.lt), [declarations/constant_overflow.lt](../conformance/declarations/constant_overflow.lt).

<a id="declarations.constant-expressions"></a>
A constant's value is a **constant expression**, built only from these parts:

- literals, with no interpolation in a string literal
- unary `-`
- tuples, lists, records and variants whose parts are constant expressions
- other constants

Arithmetic, a call, a field access, a block, an `if`, a closure, a function named as a value or anything else in it is E0326, *constant's value isn't a constant expression*. The error is at the first part, in evaluation order, that a constant expression can't hold.

Outside `std` ([declarations.native-items](#declarations.native-items)), a hole is no exception, so `const LATER: i64 = ?` is E0326. E0326 is an error of the constant's types, after which its hole gets no warning ([errors.phases](18-errors.md#errors.phases)).

Tests: [declarations/constant_expressions.lt](../conformance/declarations/constant_expressions.lt), [declarations/constants](../conformance/declarations/constants/), [declarations/non_constant_initializers.lt](../conformance/declarations/non_constant_initializers.lt).

<a id="declarations.constant-cycles"></a>
Constants must not refer to one another in a cycle, nor a constant to itself. Each cycle is one error, E0327, *constants in a cycle*, at the last of the declarations of its constants.

Tests: [declarations/constant_cycles.lt](../conformance/declarations/constant_cycles.lt), [declarations/duplicate_cycles.lt](../conformance/declarations/duplicate_cycles.lt).

<a id="declarations.constants-in-patterns"></a>
A constant's name is uppercase, so a constant can stand in a pattern, where it matches the values equal to it ([patterns.constants](09-patterns.md#patterns.constants)).

Tests: [declarations/const_lowercase.lt](../conformance/declarations/const_lowercase.lt), [declarations/constants](../conformance/declarations/constants/), [patterns/float_patterns.lt](../conformance/patterns/float_patterns.lt), [patterns/pattern_forms.lt](../conformance/patterns/pattern_forms.lt).

## Methods and tests

<a id="declarations.methods"></a>
Methods, and a type's other functions and constants, are declared in `impl` blocks ([traits.impl-blocks](11-traits.md#traits.impl-blocks)). `self` exists only in their methods ([traits.methods](11-traits.md#traits.methods)).

Tests: [declarations/functions.lt](../conformance/declarations/functions.lt), [names/self_outside_method.lt](../conformance/names/self_outside_method.lt).

<a id="declarations.tests"></a>
Tests are declared with `test` and a name ([program.test-declarations](04-programs.md#program.test-declarations)).

Tests: [program/test_names_per_module](../conformance/program/test_names_per_module/), [program/tests_and_examples.lt](../conformance/program/tests_and_examples.lt).
