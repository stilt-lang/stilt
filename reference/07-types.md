# 7. Types and generics

This chapter states how the types of a body are inferred, how fields are read, and how fields are read through an `Option`. It then gives the generic forms beyond a declared function's type parameters:

- polymorphic function types and polymorphic recursion;
- lazy values;
- anonymous records, record bounds and update;
- variadic generics;
- value parameters, and the fixed-size arrays they give.

Declared types and generic functions are in [Declarations](10-declarations.md), bounds are in [Traits and methods](11-traits.md), and the forms whose types this chapter gives are in [Expressions](08-expressions.md).

## Inference

<a id="types.inferred-per-body"></a>
Types are inferred within each body: a function's body, a test's body, a doc example or a constant's value. A body's types depend on the signatures of the items it uses, never on another body.

Tests: [effects/later_effects.lt](../conformance/effects/later_effects.lt), [numerics/literal_defaults.lt](../conformance/numerics/literal_defaults.lt), [numerics/literal_defaults_rejected.lt](../conformance/numerics/literal_defaults_rejected.lt), [traits/bound_argument_left_open.lt](../conformance/traits/bound_argument_left_open.lt), [types/independent_errors.lt](../conformance/types/independent_errors.lt).

<a id="types.no-type-arguments"></a>
Expressions never take type arguments. In an expression, `<` always means less-than, so `parse<i64>("1")` is a chain of comparisons, which is a syntax error (E0100). A generic function, variant or type named in an expression is instantiated afresh at each use. Its type arguments come from inference and annotations, as in `let m: Map<str, f64> = Map.new()`.

Tests: [declarations/generic_function_as_value.lt](../conformance/declarations/generic_function_as_value.lt), [declarations/type_arguments_inferred.lt](../conformance/declarations/type_arguments_inferred.lt), [expressions/less_than_not_generics.lt](../conformance/expressions/less_than_not_generics.lt), [expressions/no_type_arguments.lt](../conformance/expressions/no_type_arguments.lt), [traits/associated_generic_function.lt](../conformance/traits/associated_generic_function.lt).

<a id="types.expected-types"></a>
A body is checked in evaluation order ([values.left-to-right](05-values.md#values.left-to-right)). An expression is checked against its **expected type**, the type its context expects, where there is one. The expected type is one of these:

- an annotation;
- a parameter's type;
- a declared return type;
- a field's type;
- the type that an earlier element or branch established;
- for the right operand of an operator whose operands have one type, the left operand's type ([expressions.right-operand](08-expressions.md#expressions.right-operand)).

A block checked against a type passes it to its final expression. A block without a final expression has type `()`.

Tests: [expressions/branch_blocks.lt](../conformance/expressions/branch_blocks.lt), [expressions/expected_types.lt](../conformance/expressions/expected_types.lt), [expressions/expected_types_accepted.lt](../conformance/expressions/expected_types_accepted.lt), [expressions/if_branches.lt](../conformance/expressions/if_branches.lt), [expressions/key_path_annotated.lt](../conformance/expressions/key_path_annotated.lt), [patterns/arm_types.lt](../conformance/patterns/arm_types.lt).

<a id="types.mismatch"></a>
A **type mismatch** is an expression whose type differs from its expected type. It is E0311, *mismatched types*, at that expression.

Tests: [expressions/block_final_expression.lt](../conformance/expressions/block_final_expression.lt), [expressions/if_let_types.lt](../conformance/expressions/if_let_types.lt), [handlers/answer_types.lt](../conformance/handlers/answer_types.lt), [std/filter_map_rejected.lt](../conformance/std/filter_map_rejected.lt), [std/option_filter_rejected.lt](../conformance/std/option_filter_rejected.lt), [types/failed_shapes.lt](../conformance/types/failed_shapes.lt), [types/loop_types.lt](../conformance/types/loop_types.lt), [types/mismatched_types.lt](../conformance/types/mismatched_types.lt), [types/nested_function_types.lt](../conformance/types/nested_function_types.lt).

<a id="types.infinite-types"></a>
No type contains itself. Where inference would build one, as when a closure raises a value of its own type, the expression that would complete it is a type mismatch (E0311).

Tests: [types/infinite_types.lt](../conformance/types/infinite_types.lt).

<a id="types.known-types"></a>
These four positions must have types known where they are used, from what precedes them in evaluation order:

- the receiver of a method call ([traits.method-resolution](11-traits.md#traits.method-resolution));
- the base of a field access;
- an indexed value;
- the iterable of a `for`.

A type is known when its outermost constructor is. So after `var xs = []`, the call `xs.push(1)` is valid and decides the element type. A literal whose type is still open at one of these positions takes its default type ([numbers.literal-defaults](06-numbers.md#numbers.literal-defaults)). Any other unknown type there is E0312, *type that can't be inferred*, which asks for an annotation.

Tests: [expressions/closure_parameter_from_body.lt](../conformance/expressions/closure_parameter_from_body.lt), [expressions/closure_parameter_method.lt](../conformance/expressions/closure_parameter_method.lt), [expressions/fields_through_options_types.lt](../conformance/expressions/fields_through_options_types.lt), [expressions/known_outer_constructor.lt](../conformance/expressions/known_outer_constructor.lt), [expressions/known_types_in_order.lt](../conformance/expressions/known_types_in_order.lt), [expressions/unknown_types_at_use.lt](../conformance/expressions/unknown_types_at_use.lt), [types/unknown_receiver.lt](../conformance/types/unknown_receiver.lt).

<a id="types.range-bounds"></a>
The bounds of a range in a `for` aren't among the positions whose types must be known ([types.known-types](#types.known-types)). An open literal bound takes its type from how the loop variable is used, as other open literals do. So `for i in 0..10 { let b: u8 = i }` is valid.

Tests: [expressions/range_bound_out_of_range.lt](../conformance/expressions/range_bound_out_of_range.lt), [expressions/range_bounds_from_loop_variable.lt](../conformance/expressions/range_bounds_from_loop_variable.lt).

<a id="types.undecided-types"></a>
A type that the whole body leaves undecided is E0312, which asks for an annotation. So `let xs = []` is E0312 when nothing else constrains `xs`. The error is reported only when the body has no other error of names or types ([errors.undecided-types-last](18-errors.md#errors.undecided-types-last)).

Tests: [expressions/if_let_hole.lt](../conformance/expressions/if_let_hole.lt), [expressions/undecided_types.lt](../conformance/expressions/undecided_types.lt), [types/undecided_type.lt](../conformance/types/undecided_type.lt).

<a id="types.undecided-type-location"></a>
The error is at the expression that introduced the undecided type. Three kinds of expression introduce one:

- a `[]`;
- a closure parameter without an annotation;
- a use of a generic function, variant or record type, which gives each of its type parameters a type to decide.

Where inference makes several such types one, the error is at whichever of the expressions that introduced them starts first in source order. These examples follow the rule:

- `Some(Map.new())` is an error at `Map.new()`, because the type parameter of `Some` is decided as a `Map`.
- For `type Cache<K, V> = { entries: Map<K, V> }`, `Cache { entries: Map.new() }` is an error at `Cache`, which introduces the types that those of `Map.new()` become.
- `([], Map.new())` is two errors, at `[]` and at `Map.new()`, because the tuple introduces neither.

An expression that introduced several undecided types is one error. So `let m = Map.new()`, with nothing else that uses `m`, is one error, at `Map.new()`. After `let xs = []`, the call `xs.len()` decides nothing, and the error is at `[]`.

Tests: [types/undecided_after_len.lt](../conformance/types/undecided_after_len.lt), [types/undecided_in_tuple.lt](../conformance/types/undecided_in_tuple.lt), [types/undecided_inside_call.lt](../conformance/types/undecided_inside_call.lt), [types/undecided_map_once.lt](../conformance/types/undecided_map_once.lt), [types/undecided_on_two_lines.lt](../conformance/types/undecided_on_two_lines.lt), [types/undecided_record_of_generic_type.lt](../conformance/types/undecided_record_of_generic_type.lt).

<a id="types.closures-not-generalized"></a>
A `let` that binds a closure gives it one type, which is never generalized. So after `let id = |x| x`, the calls `id(1)` and `id("s")` are a type mismatch at `"s"` (E0311).

Tests: [expressions/let_closure_one_type.lt](../conformance/expressions/let_closure_one_type.lt), [expressions/let_closure_same_type.lt](../conformance/expressions/let_closure_same_type.lt).

## Fields

<a id="types.field-access"></a>
`e.f` requires `e` to have a record type with a field `f`. `e.n` requires `e` to have a tuple type with more than `n` elements. Any other field is E0313, *no such field*. A field access whose operand has type `Option` reads through it instead ([types.fields-through-option](#types.fields-through-option)). Calling a field or a tuple element that holds a function is a method call ([traits.method-resolution](11-traits.md#traits.method-resolution)).

Tests: [expressions/field_access.lt](../conformance/expressions/field_access.lt), [expressions/field_errors.lt](../conformance/expressions/field_errors.lt), [expressions/fields_through_options_nested_place.lt](../conformance/expressions/fields_through_options_nested_place.lt), [expressions/method_without_call.lt](../conformance/expressions/method_without_call.lt), [expressions/record_literal_fields.lt](../conformance/expressions/record_literal_fields.lt), [traits/field_vs_trait.lt](../conformance/traits/field_vs_trait.lt), [traits/tuple_elements.lt](../conformance/traits/tuple_elements.lt), [types/fields.lt](../conformance/types/fields.lt).

## Fields through an `Option`

<a id="types.fields-through-option"></a>
A field access `e.f`, or a tuple field access `e.0`, whose operand has type `Option<T>` reads the field of the value inside the `Option`. `e` is evaluated once. When its value is `None`, the access is `None`. When its value is `Some(x)`, the access reads the field of `x`, by this paragraph again when the type of `x` is itself an `Option`. A field that the type inside doesn't have is E0313, *no such field*. So is a field access on a `Result`, which has no fields: a `Result` is converted with `.ok()` first, as for the fallback ([expressions.option-fallback](08-expressions.md#expressions.option-fallback)).

Tests: [expressions/fallback_on_plain_field.lt](../conformance/expressions/fallback_on_plain_field.lt), [expressions/fields_through_options.lt](../conformance/expressions/fields_through_options.lt), [expressions/fields_through_options_evaluated_once.lt](../conformance/expressions/fields_through_options_evaluated_once.lt), [expressions/fields_through_options_fallback.lt](../conformance/expressions/fields_through_options_fallback.lt), [expressions/fields_through_options_missing.lt](../conformance/expressions/fields_through_options_missing.lt).

<a id="types.option-field-types"></a>
When the field has type `Option<U>`, the access has type `Option<U>`, and its value is the value of the field: the read adds no level of `Option`. When the field has any other type `F`, the access has type `Option<F>`, and its value is `Some` of the value of the field. So a path of fields holds one `Option` however many of its links are optional. In `order.customer.address.city`, where `customer` and `address` are optional and `city` is a `str`, the path has type `Option<str>`. It is `None` when either link is.

Tests: [expressions/fields_through_options.lt](../conformance/expressions/fields_through_options.lt), [expressions/fields_through_options_fallback.lt](../conformance/expressions/fields_through_options_fallback.lt), [expressions/fields_through_options_types.lt](../conformance/expressions/fields_through_options_types.lt).

<a id="types.option-field-known"></a>
The operand's type must be known at the access, as for any field access ([types.known-types](#types.known-types)). The field's type must be known there too, by its outermost constructor. Otherwise the access is E0312. Whether the read adds a level of `Option` depends on the field's type as the access's own types give it. So inside a function generic in `T`, a field of type `T` isn't an `Option`, even where a caller instantiates `T` with one.

Tests: [expressions/fields_through_options_generic_field.lt](../conformance/expressions/fields_through_options_generic_field.lt), [expressions/fields_through_options_open_field.lt](../conformance/expressions/fields_through_options_open_field.lt).

<a id="types.only-fields"></a>
No operation but a field access reads through an `Option`. A method called on an `Option` is a method of `Option` ([std.option-result-and-ordering](17-std.md#std.option-result-and-ordering)). So `order.customer.name.map(.len())` maps the `Option` of the name, and a method that only the type inside has is E0314, *no such method or member*. An index or an operator applied to an `Option` is the error that applying it to that type gives. So `o + 1` and `-o` with `o: Option<i64>` are E0317.

Tests: [expressions/fields_through_options_fallback.lt](../conformance/expressions/fields_through_options_fallback.lt), [expressions/fields_through_options_only_fields.lt](../conformance/expressions/fields_through_options_only_fields.lt), [types/operators_on_option.lt](../conformance/types/operators_on_option.lt).

<a id="types.option-field-not-place"></a>
A field read through an `Option` is a copy of a value inside it. It is not a place ([expressions.places](08-expressions.md#expressions.places)), and neither is a field or an element of one. So assigning to it, passing it `inout`, and calling on it a method that takes `inout self` are E0401, *not a place*. A read through an `Option` inside an index doesn't count: `xs[o.i else 0] = 9` assigns to a place.

Tests: [expressions/fields_through_options_nested_place.lt](../conformance/expressions/fields_through_options_nested_place.lt), [expressions/fields_through_options_not_a_place.lt](../conformance/expressions/fields_through_options_not_a_place.lt), [expressions/fields_through_options_places.lt](../conformance/expressions/fields_through_options_places.lt).

<a id="types.option-key-paths"></a>
A key path ([expressions.key-paths](08-expressions.md#expressions.key-paths)) starts with `.`, and its fields read through an `Option` as any field does. So `orders.filter_map(.customer.address.city)` gives the city of each order that has one.

Tests: [expressions/fields_through_options_key_paths.lt](../conformance/expressions/fields_through_options_key_paths.lt).

<a id="types.hole-before-dot"></a>
`?.` is not a token ([syntax.holes-before-dots](03-syntax.md#syntax.holes-before-dots)). A `?` followed by `.`, `..` or `..=` is a hole ([declarations.typed-holes](10-declarations.md#declarations.typed-holes)) followed by that token, as `(?)` followed by it is. So these forms read as follows:

- `?..3` is a range from a hole.
- `?.len()` calls `len` on a hole, whose type isn't known there (E0312).
- `t?.0` is a syntax error at the `?` (E0100).

A line that begins with `?.` doesn't continue the line before it ([lexical.terminator-insertion](02-lexical.md#lexical.terminator-insertion)).

Tests: [lexical/bare_hole_before_range.lt](../conformance/lexical/bare_hole_before_range.lt), [lexical/hole_before_dot_rejected.lt](../conformance/lexical/hole_before_dot_rejected.lt), [lexical/hole_dot_starts_line.lt](../conformance/lexical/hole_dot_starts_line.lt), [lexical/question_dot_is_two_tokens.lt](../conformance/lexical/question_dot_is_two_tokens.lt).

## Polymorphic function types

<a id="polymorphism.function-types"></a>
A function type may declare type parameters, with bounds, after `fn`, as in `fn<T: Show, U>(T, U) -> str / row`. It is then a **polymorphic function type**. Its type parameters are uppercase names, as a function's are, and each is in scope in the function type alone. Each must appear in its parameter types or its result (E0339). A type parameter with the name of one already in scope, the enclosing function's or impl block's, is E0208. These rules also hold for a polymorphic function type:

- It declares no row variable and no value parameter.
- None of its type parameters is a pack ([variadics.packs](#variadics.packs)).
- It declares no member types ([traits.member-types](11-traits.md#traits.member-types)), so each of its bounds is a trait given all its arguments.
- A constructor trait bounds none of its parameters (E0337).

This is part of the advanced tier ([polymorphism.advanced-tier](#polymorphism.advanced-tier)).

Tests: [polymorphism/arguments.lt](../conformance/polymorphism/arguments.lt), [polymorphism/placement_errors.lt](../conformance/polymorphism/placement_errors.lt).

<a id="polymorphism.placement"></a>
A polymorphic function type may be the type of one of these, and nowhere else:

- a function's parameter;
- a parameter of a function type;
- a record field;
- a variant's payload field.

Anywhere else it is E0340, *polymorphic function type out of place*. So a type argument, as in `List<fn<T>(T) -> T>`, is E0340, and so are a function's result, a local's or a closure parameter's annotation, a constant's type and a tuple's element. A value of a polymorphic function type can be passed and stored in a field, but never put in a collection.

Tests: [polymorphism/fields.lt](../conformance/polymorphism/fields.lt), [polymorphism/placement_errors.lt](../conformance/polymorphism/placement_errors.lt).

<a id="polymorphism.instantiation"></a>
A value of a polymorphic function type is called as any function value is. Each call instantiates its type parameters afresh, as naming a generic function does ([types.no-type-arguments](#types.no-type-arguments)), and so does each use of the value as an argument of a monomorphic function type. So inside `fn both(f: fn<T: Show>(T) -> str, n: i64, s: str)`, `f(n)` takes `T` to be `i64`, and `f(s)` takes it to be `str`. The bounds must hold at each instantiation, or the use is E0318, *unsatisfied bound*. Such a value may also be passed where the same polymorphic function type is expected. Two polymorphic function types are the same when they declare as many parameters, with the same bounds in the same order, and are equal after renaming the parameters in order.

Tests: [polymorphism/argument_errors.lt](../conformance/polymorphism/argument_errors.lt), [polymorphism/arguments.lt](../conformance/polymorphism/arguments.lt), [polymorphism/fields.lt](../conformance/polymorphism/fields.lt), [polymorphism/outer_parameters.lt](../conformance/polymorphism/outer_parameters.lt).

<a id="polymorphism.rigid-types"></a>
Where a polymorphic function type `fn<T: B>(…)` is expected, the argument, field value or payload is checked with each of its type parameters taken as a rigid type. A **rigid type** is a type distinct from every other, about which only its bounds are known, as a function's own type parameter is in its body.

Tests: [polymorphism/arguments.lt](../conformance/polymorphism/arguments.lt), [polymorphism/outer_parameters.lt](../conformance/polymorphism/outer_parameters.lt).

<a id="polymorphism.arguments"></a>
Three kinds of expression may be given there:

- A generic function named as a value, such as `quoted`, or `Type.f` and `Trait.m` ([traits.qualified-calls](11-traits.md#traits.qualified-calls)), when its type, instantiated, is the expected one. Each bound it needs must be one of the rigid types' bounds, or the argument is E0318, which names the bound.
- A closure literal, whose parameters take the rigid types, and whose body may use them only through their bounds (E0318). A result that doesn't have the expected type, such as `|x| x` where `str` is expected, is E0311.
- A value of the same polymorphic function type ([polymorphism.instantiation](#polymorphism.instantiation)), such as a parameter passed on.

Any other expression is a type mismatch (E0311). These are among them:

- a local bound to a closure;
- a function or closure whose type fixes a rigid type, such as an `fn(i64) -> str` where `fn<T: Show>(T) -> str` is expected;
- an argument that makes a rigid type part of a type inferred outside the argument, as `|x| x` given for `fn<T>(T) -> A` where `A` is the caller's to infer.

Tests: [polymorphism/argument_errors.lt](../conformance/polymorphism/argument_errors.lt), [polymorphism/arguments.lt](../conformance/polymorphism/arguments.lt), [polymorphism/fields.lt](../conformance/polymorphism/fields.lt), [polymorphism/outer_parameters.lt](../conformance/polymorphism/outer_parameters.lt).

<a id="polymorphism.effects-and-escaping"></a>
A parameter of a polymorphic function type passes its argument's effects through unless it is marked `escaping`, as any parameter of function type does ([effects.non-escaping-parameters](12-effects.md#effects.non-escaping-parameters)). Its row, as written, is the row of every instantiation. Implicit effects are counted as for any function value ([facts.calls-through-function-values](15-facts.md#facts.calls-through-function-values)).

Tests: [polymorphism/arguments.lt](../conformance/polymorphism/arguments.lt).

<a id="polymorphism.advanced-tier"></a>
A module that writes a polymorphic function type is in the advanced tier ([program.module-tier](04-programs.md#program.module-tier)). A module that only passes an argument to a function declared elsewhere with a parameter of one stays in core.

Checked by: the facts suite, whose `tests/facts/polymorphism.lt` carries `//~ tier: advanced`, which `just facts` checks, and the toolchain's tests of `stilt show` (`compiler/stilt-cli/tests/show.rs`).

## Polymorphic recursion

<a id="polymorphism.recursion"></a>
A generic function may call itself, or another function of its recursive group, with type arguments other than its own type parameters. For example, `depth<T>(n: Nested<T>)` calls `depth(inner)` with `inner: Nested<List<T>>`. The call is checked against the callee's written signature like any other ([declarations.function-declarations](10-declarations.md#declarations.function-declarations)). Polymorphic recursion is part of core, and raises no module's tier.

Tests: [polymorphism/inout_past_caps.lt](../conformance/polymorphism/inout_past_caps.lt), [polymorphism/outer_parameters.lt](../conformance/polymorphism/outer_parameters.lt), [polymorphism/receiver_past_caps.lt](../conformance/polymorphism/receiver_past_caps.lt), [polymorphism/recursion.lt](../conformance/polymorphism/recursion.lt), [polymorphism/recursion_past_caps.lt](../conformance/polymorphism/recursion_past_caps.lt), [variadics/recursion.lt](../conformance/variadics/recursion.lt).

## Lazy values

<a id="polymorphism.lazy-values"></a>
The module `std.lazy` declares the native type `Lazy<T>` and two native functions of `Lazy<T>`:

- `new(escaping f: fn() -> T) -> Lazy<T>` takes a function whose row is empty. So a function or closure given to `new` that performs `io` or raises is E0502, *effect that doesn't fit the row* ([effects.inference](12-effects.md#effects.inference)).
- `get(self) -> T` returns the value of `f()`. It computes the value the first time `get` is called on the `Lazy` or on any copy of it, and returns the same value after that.

A module that names `Lazy` is in the advanced tier.

Tests: [polymorphism/lazy_errors.lt](../conformance/polymorphism/lazy_errors.lt), [polymorphism/lazy_values.lt](../conformance/polymorphism/lazy_values.lt).

<a id="polymorphism.lazy-waits-for-nothing"></a>
`f` waits for nothing. A site of `locks` ([shared.locks](14-tasks.md#shared.locks)) in either of these is E0435, *`when` in a lazy value's function*, at the site, unless E0430 reports it:

- the closure literal or function given to `new`;
- the closure literal that a `let` binds to the local given to `new`.

A `when` that runs while an `f` runs panics with the kind `deadlock` before it holds anything ([shared.when-on-value-already-held](14-tasks.md#shared.when-on-value-already-held)). This holds for a `when` on the thread of `f`, and in a part of a call of `std.par` that `f` makes ([par.std-par](14-tasks.md#par.std-par)). It holds too for a `when` that `f` reaches through a function value, which no check sees. So `f` never waits for the code that asked for its value. It never reaches the `Lazy` it computes, which only a shared value could hold ([cycles.through-shared-values](14-tasks.md#cycles.through-shared-values)).

Tests: [polymorphism/lazy_deadlock.lt](../conformance/polymorphism/lazy_deadlock.lt), [polymorphism/lazy_deadlock_par.lt](../conformance/polymorphism/lazy_deadlock_par.lt), [polymorphism/lazy_locks.lt](../conformance/polymorphism/lazy_locks.lt), [polymorphism/lazy_reaches_itself.lt](../conformance/polymorphism/lazy_reaches_itself.lt).

<a id="polymorphism.lazy-unobservable"></a>
No program can observe when `f` runs, or how often, and copies of a `Lazy` share its result. `Lazy` joins no prelude, and no prelude type gains a method. `Lazy` implements none of the prelude's traits, so `==` and an interpolation of a `Lazy` are E0318.

Tests: [polymorphism/lazy_errors.lt](../conformance/polymorphism/lazy_errors.lt), [polymorphism/lazy_values.lt](../conformance/polymorphism/lazy_values.lt).

<a id="polymorphism.lazy-implicit-effects"></a>
`new` and `get` allocate ([facts.native-allocation](15-facts.md#facts.native-allocation)), and `get` has `div` ([facts.div](15-facts.md#facts.div)). The `panic`, `alloc` and `div` of the body of `f` are counted where the closure is written, or where the function is named ([facts.inference](15-facts.md#facts.inference)). So `get` adds none of the body's, and `without panic` accepts a call of `get` in a function that wrote no closure that can panic.

Tests: [implicit/allocating_natives.lt](../conformance/implicit/allocating_natives.lt), [polymorphism/lazy_limits.lt](../conformance/polymorphism/lazy_limits.lt).

## Anonymous records

<a id="records.anonymous-types"></a>
`{ f: T, g: U }` is an **anonymous record type**, which may be written wherever a type may be. It has one field or more, each named once (E0316), so `{}` is not a type. Two anonymous record types are the same type when they have the same field names with the same types, in any order. An anonymous record type is never the same as a declared record ([declarations.records](10-declarations.md#declarations.records)), whatever their fields. This is part of the advanced tier ([records.advanced-tier](#records.advanced-tier)).

Tests: [ported/swift_tuples.lt](../conformance/ported/swift_tuples.lt), [records/anonymous.lt](../conformance/records/anonymous.lt), [records/anonymous_errors.lt](../conformance/records/anonymous_errors.lt).

<a id="records.no-home"></a>
An anonymous record type has no home module. So it has no inherent functions, and no trait impls but the structural ones ([records.field-order](#records.field-order)). No type has an alias ([declarations.no-aliases](10-declarations.md#declarations.no-aliases)), so `type P = { … }` declares a nominal record, not a name for an anonymous type.

Tests: [records/anonymous.lt](../conformance/records/anonymous.lt).

<a id="records.field-order"></a>
An anonymous record has the structural `Eq`, `Ord`, `Hash` and `Show` when every field's type has them, as a declared record does ([traits.structural-impls](11-traits.md#traits.structural-impls)). In comparing, hashing and showing, a declared record's impls take its fields in declaration order. An anonymous record's impls take its fields in the alphabetical order of their names, by their bytes, as in `{ age: 36, name: "Ada" }`. The written order isn't part of the type.

Tests: [records/anonymous.lt](../conformance/records/anonymous.lt).

<a id="records.anonymous-literals"></a>
`{ f: e, g }` is an **anonymous record literal**. A `{` followed by a field name and a `:` begins one, where a block or a struct literal's braces would otherwise begin. Every field after the first may be written `g` for `g: g`. So `{ x }` is a block, and `{ x: x }` a record. The fields are evaluated in written order. A literal's type is the anonymous record type of its fields, each of the type of its value, as the elements of a list literal are: `{ n: panic("no name") }` is a `{ n: Never }`. Where an anonymous record of the same fields is expected, each field is checked against the expected field's type, to which a value of type `Never` converts ([declarations.never](10-declarations.md#declarations.never)). It is never a declared record, even where one is expected (E0311).

Tests: [ported/swift_tuples.lt](../conformance/ported/swift_tuples.lt), [records/anonymous.lt](../conformance/records/anonymous.lt), [records/anonymous_errors.lt](../conformance/records/anonymous_errors.lt), [records/anonymous_never.lt](../conformance/records/anonymous_never.lt).

<a id="records.anonymous-patterns"></a>
`{ f, g: p }` matches an anonymous record. `{ f, .. }` matches any record whose type is known to have a field `f` ([records.record-bounds](#records.record-bounds)): a declared record, an anonymous one, or a type parameter whose bound names `f`. Without `..`, a pattern must name every field of the anonymous type it matches (E0316). So a pattern on a type parameter, whose bound never names every field, ends with `..`. A declared record's pattern is written `Name { … }` ([patterns.pattern-forms](09-patterns.md#patterns.pattern-forms)).

Tests: [records/catch_patterns.lt](../conformance/records/catch_patterns.lt), [records/update_advanced.lt](../conformance/records/update_advanced.lt), [records/update_errors.lt](../conformance/records/update_errors.lt).

## Record bounds

<a id="records.record-bounds"></a>
A bound may be a **record bound**, `P: { f: T, .. }`, alone or with traits, as in `P: { name: str, .. } + Show`. A record bound may stand on the type parameters of functions and impl blocks, and in a `where` clause on a member type ([traits.where](11-traits.md#traits.where)). A type meets it when it is a declared or anonymous record that has each field named, with exactly that type once the record's type arguments are substituted. So `Box<i64>`, declared `{ v: T }`, meets `{ v: i64, .. }`. Any other type is E0318, *unsatisfied bound*, which names the field, and so is a record that lacks a field or has it with another type.

Tests: [checking/open_record_with_unknown_names.lt](../conformance/checking/open_record_with_unknown_names.lt), [records/bound_errors.lt](../conformance/records/bound_errors.lt), [records/bound_without_rest.lt](../conformance/records/bound_without_rest.lt), [records/bounds.lt](../conformance/records/bounds.lt).

<a id="records.bound-fields"></a>
A field reached through a record bound behaves as a record's field does. It is read, written through an `inout` or `var` place ([modes.what-can-be-modified](13-modes.md#modes.what-can-be-modified)), and read through an `Option` ([types.fields-through-option](#types.fields-through-option)). A record bound's `..` is required: `P: { f: T }` is E0341, whose fix adds it. Such a bound is read as if it had its `..`. So a field it names is reached through it with no other diagnostic, and a type that lacks the field doesn't meet it.

Tests: [records/bound_errors.lt](../conformance/records/bound_errors.lt), [records/bound_without_rest.lt](../conformance/records/bound_without_rest.lt), [records/bounds.lt](../conformance/records/bounds.lt), [records/closed_bound_read_as_open.lt](../conformance/records/closed_bound_read_as_open.lt).

<a id="records.open-parameter-types"></a>
A parameter's type may be an **open record type**, `{ f: T, .. }`. It stands for a hidden, unnamed type parameter of the function with that record bound: `fn greet(p: { name: str, .. })` means `fn greet<P: { name: str, .. }>(p: P)`. Each open type written is its own type parameter. An open record type anywhere else is E0341, *open record type out of place*. That includes a field, a result, a type argument, a local's annotation and a parameter of a function type. The fix names a type parameter with the bound.

Tests: [checking/open_record_with_unknown_names.lt](../conformance/checking/open_record_with_unknown_names.lt), [records/bound_errors.lt](../conformance/records/bound_errors.lt), [records/bounds.lt](../conformance/records/bounds.lt).

## Update

<a id="records.update"></a>
`{ ..base, f: e }` builds a record of the type of `base`, with the fields written replaced and every other field copied from `base`. This form applies to a `base` of an anonymous record type, or of a type parameter with a record bound. For a declared record it is E0311, whose fix names the record. `Name { ..base, f: e }` does the same for a declared record, and `base` has type `Name<…>`. Update on a declared record is part of core. Update on any other record is part of the advanced tier.

Tests: [records/update.lt](../conformance/records/update.lt), [records/update_advanced.lt](../conformance/records/update_advanced.lt), [records/update_errors.lt](../conformance/records/update_errors.lt), [records/update_of_a_declared_record_as_an_operand.lt](../conformance/records/update_of_a_declared_record_as_an_operand.lt).

<a id="records.update-fields"></a>
`base` is evaluated first, then the fields in written order. Each field written must be one of the type's fields, or of a bound's fields for a type parameter (E0313). It must be written at most once (E0316), and have the field's type (E0311). With no field written, the update is a copy of `base`. Update never adds or removes a field, so its type is always the type of `base`.

Tests: [records/update.lt](../conformance/records/update.lt), [records/update_errors.lt](../conformance/records/update_errors.lt).

<a id="records.advanced-tier"></a>
A module that writes any of these is in the advanced tier ([program.module-tier](04-programs.md#program.module-tier)):

- an anonymous record type;
- an anonymous record literal or pattern;
- a record bound;
- an open record type;
- an update of an anonymous or bounded record.

A module that only calls a function declared elsewhere with a record bound stays in core.

Checked by: the facts suite, whose `tests/facts/records.lt` carries `//~ tier: advanced`, which `just facts` checks, and the toolchain's tests of `stilt show` (`compiler/stilt-cli/tests/show.rs`).

## Variadic generics

<a id="variadics.packs"></a>
`..Ts` among a function's generics, or among a type's parameters, declares a **pack**: a type parameter that stands for a sequence of zero or more types, its elements. A function may declare several packs. A type may declare at most one, as its last parameter (E0344), so the arguments of `Row<i64, str, bool>` after the others are the pack's. A pack may take bounds, as `..Ts: Show`, which each element meets ([traits.bounds](11-traits.md#traits.bounds)). A trait's parameters, a constructor trait's `Self` and a polymorphic function type's parameters are never packs (E0344). This is part of the advanced tier ([variadics.advanced-tier](#variadics.advanced-tier)).

Tests: [variadics/misplaced_pack_named_bare.lt](../conformance/variadics/misplaced_pack_named_bare.lt), [variadics/placement_errors.lt](../conformance/variadics/placement_errors.lt), [variadics/row_recursion.lt](../conformance/variadics/row_recursion.lt), [variadics/spreads.lt](../conformance/variadics/spreads.lt), [variadics/types.lt](../conformance/variadics/types.lt).

<a id="variadics.type-spreads"></a>
A pack is written only spread, as `..T`, where `T` is a type that names one or more packs. A spread stands among the elements of a tuple type or the parameters of a function type, as in `(..Ts)`, `(..List<Ts>, i64)` and `fn(..Ts) -> R`. A spread names exactly one pack, perhaps more than once. It stands for one element for each of the pack's elements, with the pack replaced by that element. So `(..List<Ts>)` at `Ts = (i64, str)` is `(List<i64>, List<str>)`, and `(..Ts, ..Us)` places two packs side by side. A pack written outside a spread, a spread that names no pack or two, and a spread inside a spread are E0343, *malformed spread*. A tuple type with a spread and no other element is the tuple of its elements. So `(..Ts)` at one element `T` is `(T,)`, and at none is `()`.

Tests: [variadics/errors.lt](../conformance/variadics/errors.lt), [variadics/function_type_of_no_pack.lt](../conformance/variadics/function_type_of_no_pack.lt), [variadics/spreads.lt](../conformance/variadics/spreads.lt), [variadics/types.lt](../conformance/variadics/types.lt).

<a id="variadics.pack-inference"></a>
At a use of a generic function, each pack is inferred from the types of the arguments, as any type parameter is ([types.no-type-arguments](#types.no-type-arguments)). Where a tuple type with a spread is expected, the pack comes from the tuple's elements. Where a function type with a spread is expected, it comes from the function's parameter types, and a closure literal's parameters, written or not, give the pack its length. A type's pack is given by its arguments after the others. A pack that nothing determines is E0312.

Tests: [variadics/placement_errors.lt](../conformance/variadics/placement_errors.lt), [variadics/spreads.lt](../conformance/variadics/spreads.lt), [variadics/types.lt](../conformance/variadics/types.lt).

<a id="variadics.pack-tuples"></a>
A **pack tuple** is a value whose type is a tuple type with a spread. It may be passed, returned, stored and copied as a tuple is. It may be compared or shown as a tuple is when its elements meet `Eq` or `Show` through the pack's bounds ([traits.structural-impls](11-traits.md#traits.structural-impls)). Its arity isn't known in the body. So a pattern that destructures it, `.0` on it, `for` over it and indexing it are E0342.

Tests: [variadics/errors.lt](../conformance/variadics/errors.lt), [variadics/types.lt](../conformance/variadics/types.lt).

<a id="variadics.spread-expressions"></a>
Three expressions take a pack tuple apart by mapping over it:

- `(..e)` builds a tuple. `e` is evaluated once for each element, from the first to the last, with each pack tuple named in `e` standing for its element there. The results are the tuple's elements. Plain elements may stand beside the spread, as in `(..e, x)`.
- `[..e]` builds a list of the same results. The type of `e` must name no pack, so that every element has it (E0311), as in `[..lists.len()]`.
- `f(..e)`, among a call's arguments, passes the results as arguments, where `f` has a function type with a spread.

The arguments of a call of a function type with a spread have, together, the type of a tuple of them, which must be the tuple of its parameters. So in the body that declares the pack, plain arguments, as in `g(1, 2)` or `g()` for `g: fn(..Ts) -> i64`, are E0311, *mismatched types*, whatever their number.

Tests: [checking/spread_into_a_broken_parameter.lt](../conformance/checking/spread_into_a_broken_parameter.lt), [variadics/dynamic_call.lt](../conformance/variadics/dynamic_call.lt), [variadics/errors.lt](../conformance/variadics/errors.lt), [variadics/hole_called_with_a_spread.lt](../conformance/variadics/hole_called_with_a_spread.lt), [variadics/spread_of_no_pack.lt](../conformance/variadics/spread_of_no_pack.lt), [variadics/spreads.lt](../conformance/variadics/spreads.lt).

<a id="variadics.spread-checks"></a>
A spread expression must name at least one pack tuple. All the pack tuples it names must have types that spread one pack, so that they have the same length (E0343). Naming one of them inside a closure literal or a nested spread in `e` is E0343. A spread that names no pack tuple still has its `e` checked, as any `e` is, with no expected type. So a mistake of its own in `e` is reported too. A spread's effects are those of `e`, once for each element, in order. So a `raise` in `e` passes through as in any expression, and `try` marks the calls in it ([effects.marking](12-effects.md#effects.marking)).

Tests: [checking/call_spreading_a_broken_tuple.lt](../conformance/checking/call_spreading_a_broken_tuple.lt), [checking/spread_of_a_broken_item.lt](../conformance/checking/spread_of_a_broken_item.lt), [checking/spread_of_a_broken_tuple.lt](../conformance/checking/spread_of_a_broken_tuple.lt), [variadics/effects.lt](../conformance/variadics/effects.lt), [variadics/errors.lt](../conformance/variadics/errors.lt), [variadics/spread_of_no_pack.lt](../conformance/variadics/spread_of_no_pack.lt).

<a id="variadics.empty-pack"></a>
A pack may have no elements: `zip(())` takes `Ts` to be empty, `(..e)` is `()`, `[..e]` is `[]` of the type that the context gives it, and `f(..e)` passes nothing.

Tests: [variadics/spreads.lt](../conformance/variadics/spreads.lt).

<a id="variadics.advanced-tier"></a>
A module that declares a pack is in the advanced tier ([program.module-tier](04-programs.md#program.module-tier)). A module that only calls a function declared elsewhere with a pack stays in core.

Checked by: the facts suite, whose `tests/facts/variadics.lt` carries `//~ tier: advanced`, which `just facts` checks, and the toolchain's tests of `stilt show` (`compiler/stilt-cli/tests/show.rs`).

## Value parameters

<a id="generics.value-parameters"></a>
A function's generics, a type's parameters and an impl's generics may hold **value parameters**, beside type parameters and, for a function, row variables ([declarations.function-declarations](10-declarations.md#declarations.function-declarations)). A value parameter is written `name: T`, as `n: i64`. Its name is a `lower` identifier, as every value's is ([lexical.case](02-lexical.md#lexical.case)), so `<n: i64>` is a value parameter and `<e>` a row variable. As for type parameters, the names of one list of generics must be distinct, and so must those of an impl's generics and its members' generics (E0208). A value parameter's type is an integer type or `bool`. Any other type, as `f64`, `str` or a declared type, is E0345 at the type. This is part of the meta tier ([generics.meta-tier](#generics.meta-tier)).

Tests: [generics/declaration_errors.lt](../conformance/generics/declaration_errors.lt), [generics/declarations.lt](../conformance/generics/declarations.lt).

<a id="generics.value-parameter-positions"></a>
A trait's parameters, an effect's generics and a polymorphic function type's generics are type parameters only. A value parameter among them is a syntax error (E0100), as a row variable among a function type's generics is. A pack is a list of types, so `..n: i64` is a syntax error too.

Tests: [generics/placement_errors.lt](../conformance/generics/placement_errors.lt).

<a id="generics.value-parameters-determined"></a>
A function's value parameter must appear, outside every row, in the type of one of its parameters or in its result type. One that appears in neither is E0346 at the parameter, unless its own type is the error type or one that E0345 reports, which leaves it the error type ([errors.error-type](18-errors.md#errors.error-type)): so `<x: f64>` is E0345 alone. Appearing is enough here. A use that still leaves it undetermined is E0312 at the use, as for a type parameter, as a closure literal given for `g: fn(Array<i64, n>)` does. An impl's type is its constructor applied to the impl's parameters, value and type, each once ([traits.impl-blocks](11-traits.md#traits.impl-blocks)). So `impl Mod<7>` and `impl<p: u64> Mod<p, p>` are E0302, as `impl List<i64>` is, and so is an impl's value parameter that its type doesn't name. A type is always written with its arguments ([declarations.type-arguments](10-declarations.md#declarations.type-arguments)), so a type's value parameter may appear in none of its fields, as `p` doesn't in `type Mod<p: u64> = { value: u64 }`.

Tests: [generics/declaration_errors.lt](../conformance/generics/declaration_errors.lt), [generics/declarations.lt](../conformance/generics/declarations.lt), [generics/inference_errors.lt](../conformance/generics/inference_errors.lt).

<a id="generics.value-parameters-in-body"></a>
A value parameter's name is an immutable value of its type, as a constant is, in the body of its function and in the members of its impl. `0..n`, `n * 2` and `f(n)` read it. It hides an item of the same name, as a parameter does ([expressions.shadowing](08-expressions.md#expressions.shadowing)). A binding in those bodies named as a value parameter in scope is E0348 at the binding. That holds for a parameter, a `let`, a `var`, a pattern's variable and a closure's parameter.

Tests: [generics/binding_errors.lt](../conformance/generics/binding_errors.lt), [generics/declarations.lt](../conformance/generics/declarations.lt), [generics/in_body.lt](../conformance/generics/in_body.lt), [generics/value_parameter_as_a_type.lt](../conformance/generics/value_parameter_as_a_type.lt).

<a id="generics.value-arguments"></a>
Wherever a type is written, a type with value parameters takes a value argument in the position of each, as `Mod<7>`, `Mod<PRIME>`, `Mod<p>` and `Array<i64, n>` do. It is otherwise written as any generic type is, with exactly as many arguments as it has parameters (E0300). A value argument is one of these:

- An integer literal, with an optional `-`, or `true` or `false`, which has the parameter's type. An integer literal out of that type's range is E0320, and a literal of another type, as in `Mod<true>`, is E0311.
- A constant, named by its path, of the parameter's type (E0311).
- A value parameter in scope, of the parameter's type (E0311).

Arithmetic, as in `Array<i64, n + 1>`, is a syntax error (E0100).

Tests: [generics/argument_errors.lt](../conformance/generics/argument_errors.lt), [generics/placement_errors.lt](../conformance/generics/placement_errors.lt), [generics/value_arguments](../conformance/generics/value_arguments/).

<a id="generics.value-argument-names"></a>
Whether an argument is for a type parameter or a value parameter is read from the declaration of its constructor. An `Upper` path there is looked up as a constant for a value parameter, and as a type for a type parameter. A `lower` name is looked up among the primitive type names, then the value parameters in scope, then every other name in scope where the type is written, locals included. A name found anywhere but where its position needs it is E0347 at the argument. These are such names:

- for a value parameter, a type, as in `Mod<i64>`, a local, a function or the variable of a `comptime for` ([meta.staged-loops](16-meta.md#meta.staged-loops));
- for a type parameter, a literal, a constant, a value parameter, a function, a local or a module, as in `List<3>`, `List<PRIME>`, `List<n>` or `List<print>`.

A name found nowhere is E0211.

Tests: [generics/argument_errors.lt](../conformance/generics/argument_errors.lt), [generics/arguments_of_a_broken_path.lt](../conformance/generics/arguments_of_a_broken_path.lt), [generics/type_argument_names.lt](../conformance/generics/type_argument_names.lt).

<a id="generics.equal-types"></a>
Two types are equal when their constructors are equal and their arguments are pairwise equal. Type arguments are compared as types, and value arguments by value. So `Mod<PRIME>` and `Mod<1_000_000_007>` are one type when `PRIME` is `1_000_000_007`. A value parameter is equal only to itself, whatever value a call gives it. So in the body of `f<n: i64, m: i64>`, `Array<i64, n>` is neither `Array<i64, 3>` nor `Array<i64, m>` (E0311), even when every call gives `3`. A diagnostic shows a value argument as its value, in decimal, or as the name of the value parameter it is.

Tests: [generics/equal_type_errors.lt](../conformance/generics/equal_type_errors.lt), [generics/equal_types.lt](../conformance/generics/equal_types.lt), [generics/value_arguments](../conformance/generics/value_arguments/).

<a id="generics.constant-arguments"></a>
A constant given as a value argument is computed while the program is checked, once, for this alone. That computation is no use of its value, so a run still evaluates the constant at its first use ([declarations.constant-declarations](10-declarations.md#declarations.constant-declarations)). A constant whose computation would panic, as a unary `-` that overflows does, is E0347 at each argument that gives it.

Tests: [checking/broken_constant_as_value_argument.lt](../conformance/checking/broken_constant_as_value_argument.lt), [generics/argument_errors.lt](../conformance/generics/argument_errors.lt), [generics/value_arguments](../conformance/generics/value_arguments/).

<a id="generics.value-parameter-inference"></a>
A call writes no value arguments. Each use of a function with value parameters instantiates them afresh, as it does its type parameters ([types.no-type-arguments](#types.no-type-arguments)). They are found by unifying its parameters' types with its arguments' types, and its result type with the type the call is expected to have ([types.expected-types](#types.expected-types)). A value parameter that nothing determines at a use is E0312, as a type parameter is, as in `let z = array.fill(0)` with no annotation. A record literal or a variant of a type with value parameters gets them the same way, from the expected type, as `let a: Mod<7> = Mod { value: 3 }` does. A generic function named as a value takes them from the expected function type, as `let f: fn(Mod<7>, Mod<7>) -> Mod<7> = add` does.

Tests: [generics/declarations.lt](../conformance/generics/declarations.lt), [generics/inference.lt](../conformance/generics/inference.lt), [generics/inference_errors.lt](../conformance/generics/inference_errors.lt).

<a id="generics.meta-tier"></a>
A module that declares a value parameter is in the meta tier ([program.module-tier](04-programs.md#program.module-tier)). A module that only names a type with value arguments, as `array.Array<i64, 3>` or `Mod<7>`, stays in its tier, as one that only uses a macro does ([macros.advanced-tier](16-meta.md#macros.advanced-tier)). So does a module that only uses a function with value parameters. So `std.array` is a meta module, and a core module that uses it stays a core module.

Tests: [generics/tier](../conformance/generics/tier/).

## Arrays

<a id="generics.arrays"></a>
The module `std.array` declares the native type `Array<T, n: i64>`, a sequence of exactly `n` values of type `T`, and these functions:

| Function | Behaviour |
| --- | --- |
| `array.fill<T, n: i64>(x: T) -> Array<T, n>` | `n` copies of `x`; panics with `bounds` when `n` is negative |
| `array.from_list<T, n: i64>(xs: List<T>) -> Option<Array<T, n>>` | The elements of `xs` in order, or `None` unless `xs.len() == n` |
| `len(self) -> i64` | `n` |
| `to_list(self) -> List<T>` | The elements in order |
| `map<U>(self, f: fn(T) -> U) -> Array<U, n>` | `f` of each element, called in order; `f`'s effects pass through ([effects.non-escaping-parameters](12-effects.md#effects.non-escaping-parameters)) |

`std.array` is not part of the prelude, so a module names it with `use std.array`, as in `array.Array<i64, 3>` ([program.what-use-binds](04-programs.md#program.what-use-binds)).

Tests: [generics/array_fill_negative.lt](../conformance/generics/array_fill_negative.lt), [generics/array_functions.lt](../conformance/generics/array_functions.lt), [generics/declarations.lt](../conformance/generics/declarations.lt).

<a id="generics.array-sizes"></a>
An array's size is an `i64`. A negative integer literal or a constant below zero given as the size of `Array` is E0347 at the argument, so `Array<i64, -1>` is an error where it is written. A negative size can also reach `Array` through a value parameter, from an argument written for another type, as `Grid<-1>` does for `type Grid<k: i64> = { cells: Array<i64, k> }`. Such a size makes a type that no value has: no literal has its length, `from_list` gives `None`, and `fill` panics.

Tests: [generics/array_errors.lt](../conformance/generics/array_errors.lt), [generics/array_fill_negative.lt](../conformance/generics/array_fill_negative.lt).

<a id="generics.array-literals"></a>
A list literal whose expected type is `Array<T, n>` makes an array. Its elements, written in order, must each have type `T`, and there must be exactly `n` of them, or the literal is E0311, which names both lengths. A spread among its elements ([variadics.spread-expressions](#variadics.spread-expressions)) is E0311. In the body of `f<n: i64>`, `[1, 2]` is no `Array<i64, n>` ([generics.equal-types](#generics.equal-types)). The right operand of an operator whose operands have one type is expected to have the left operand's type. So `v == [1, 2, 3]` compares two arrays. In `[1, 2, 3] == v`, the literal, which nothing expects to be an array, is a `List`, and `v` is E0311. Where no `Array` type is expected, a list literal is a `List`.

Tests: [generics/array_errors.lt](../conformance/generics/array_errors.lt), [generics/array_functions.lt](../conformance/generics/array_functions.lt).

<a id="generics.array-elements"></a>
`a[i]` reads the element at index `i` of an array, for an `i64` index. It is a place, as a list's element is ([expressions.places](08-expressions.md#expressions.places)), so `a[i] = v`, `a[i] += 1` and `inout a[i]` write it. Each of these panics with `bounds` unless `0 ≤ i < n`, as a list's index does ([std.lists](17-std.md#std.lists)). An array has only the members of [generics.arrays](#generics.arrays) and its structural impls, so `a.get(0)` and `a.push(1)` are E0314. An array is a value ([values.value-semantics](05-values.md#values.value-semantics)). Copying one copies its elements, and writing one through a `var` or an `inout` parameter changes that copy only.

Tests: [generics/array_bounds.lt](../conformance/generics/array_bounds.lt), [generics/array_errors.lt](../conformance/generics/array_errors.lt), [generics/array_values.lt](../conformance/generics/array_values.lt), [verification/order_block_length.lt](../conformance/verification/order_block_length.lt), [verification/range_arrays.lt](../conformance/verification/range_arrays.lt), [verification/range_arrays_rejected.lt](../conformance/verification/range_arrays_rejected.lt).

<a id="generics.array-iteration"></a>
A `for` over an `Array<T, n>` yields its elements, of type `T`, in order ([expressions.for-iterables](08-expressions.md#expressions.for-iterables)).

Tests: [generics/array_values.lt](../conformance/generics/array_values.lt), [generics/in_body.lt](../conformance/generics/in_body.lt).

<a id="generics.array-patterns"></a>
A list pattern ([patterns.pattern-forms](09-patterns.md#patterns.pattern-forms)) matches an array when its length fits the array's size. `[p₁, …, pₖ]` fits when `k` is the size, and `[p₁, …, pₖ, ..]` when `k` is at most the size. The size is compared while the program is checked, as value arguments are ([generics.equal-types](#generics.equal-types)). So against `Array<i64, n>` only `[..]` fits, and `[x, y]` doesn't. A pattern whose length doesn't fit is E0311, and so is a rest that binds a name, as in `[x, ..rest]`.

Tests: [generics/array_errors.lt](../conformance/generics/array_errors.lt), [generics/array_patterns.lt](../conformance/generics/array_patterns.lt).

<a id="generics.array-exhaustiveness"></a>
For exhaustiveness and unreachable arms ([patterns.algorithm](09-patterns.md#patterns.algorithm)), an array of size `k` is matched as a tuple of `k` elements. `[p₁, …, pⱼ, ..]` is matched as that tuple with `_` after its `j` patterns. So a list pattern on an array is irrefutable when its elements are ([patterns.irrefutable-positions](09-patterns.md#patterns.irrefutable-positions)). `let [x, y, z] = v` needs no `else`, and `let [x, y, z] = v else e` means `let [x, y, z] = (v else e)`, as for every irrefutable pattern ([patterns.let-else](09-patterns.md#patterns.let-else)).

Tests: [generics/array_errors.lt](../conformance/generics/array_errors.lt), [generics/array_patterns.lt](../conformance/generics/array_patterns.lt).

<a id="generics.array-traits"></a>
An array has the structural impls of [traits.structural-impls](11-traits.md#traits.structural-impls) when its element type has them, as a list does:

- `Eq` compares the elements in order.
- `Ord` orders arrays by their elements, as lists are ordered.
- `Hash` hashes the elements in order.
- `Show` writes an array as a list is written, as `[1, 2, 3]`.

Tests: [generics/array_traits.lt](../conformance/generics/array_traits.lt).

<a id="generics.large-arrays"></a>
Implementations support every array type whose elements number at most 65,536 in all, each element of a nested array counted. So `Array<Array<i64, 300>, 300>` has 90,000. A larger one may end the run as running out of memory or stack does ([program.exit-statuses](04-programs.md#program.exit-statuses)), as a call deeper than [program.recursion-depth](04-programs.md#program.recursion-depth) asks may. No array holds more than 2^48 elements in any implementation, as no list does. Making one ends the run as running out of memory does, with status 134 ([facts.greatest-length](15-facts.md#facts.greatest-length)).

Tests: [generics/large_array.lt](../conformance/generics/large_array.lt).

<a id="generics.array-effects"></a>
An array's elements are stored inline, as a record's fields are. So making, copying, reading and writing an array allocate nothing, and only `to_list` and the calls of the argument of `map` add `alloc` ([facts.allocation](15-facts.md#facts.allocation)). Two things add `panic` ([effects.without-panic](12-effects.md#effects.without-panic)): calling `fill`, and reading or writing an element at an index that no rule of acceptance proves below the size ([facts.range-loops](15-facts.md#facts.range-loops), [facts.guards](15-facts.md#facts.guards)).

Tests: [effects/natives_under_limits.lt](../conformance/effects/natives_under_limits.lt), [generics/array_effects.lt](../conformance/generics/array_effects.lt), [promises/in_place_elements.lt](../conformance/promises/in_place_elements.lt).
