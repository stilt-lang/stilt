# 11. Traits and methods

An `impl` block gives a type its methods, associated functions and constants. A trait is a set of function signatures that types implement, and a bound limits a type parameter to the types that implement traits. A method call is resolved from the type of its receiver alone. The prelude declares four traits behind operators, map keys and interpolation, and types get structural impls of them without writing one. Types and functions are declared as [Declarations](10-declarations.md) says, and inference is that of [Types and generics](07-types.md).

## Inherent impl blocks

<a id="traits.impl-blocks"></a>
A type's home module may hold blocks of the form `impl<A, …> Type<A, …> { … }`, which hold functions and constants of the type. Such a block is an **inherent impl**. No other module may hold one: an inherent impl outside the type's module is E0301, *inherent impl outside the type's module*. So a program adds methods to a built-in type, whose home is `std.prelude`, only through a trait of its own.

The block's type must be a type constructor of the module applied to the block's parameters, type and value, each once, in any order. Any other type is E0302, *invalid impl type*. `impl<T> List<T>` is valid in `std.prelude`, while `impl List<i64>`, `impl<A> Pair<A, A>`, `impl<A, B, C> Pair<A, B>` and `impl (i64, i64)` are not.

Tests: [polymorphism/receiver_past_caps.lt](../conformance/polymorphism/receiver_past_caps.lt), [ported/temperature_conversion.lt](../conformance/ported/temperature_conversion.lt), [traits/foreign_impls.lt](../conformance/traits/foreign_impls.lt), [traits/impl_type.lt](../conformance/traits/impl_type.lt), [traits/inherent_impl_elsewhere](../conformance/traits/inherent_impl_elsewhere/), [traits/inherent_methods.lt](../conformance/traits/inherent_methods.lt), [types/error_type_cascades.lt](../conformance/types/error_type_cascades.lt).

<a id="traits.methods"></a>
A function whose first parameter is `self` is a **method**, called as `x.m(…)`. `self` may carry the mode `inout`, as `inout self`, under which the method modifies the receiver's place ([modes.what-can-be-modified](13-modes.md#modes.what-can-be-modified)). Only the functions of `impl` and trait blocks take `self`, and `self` exists only in methods.

`Self` is the block's type in an `impl` block, and in a trait it is the type that implements the trait. `Self` exists nowhere else. `self` or `Self` anywhere else is E0215, *`self` or `Self` where it doesn't exist*.

Tests: [declarations/functions.lt](../conformance/declarations/functions.lt), [expressions/fields_through_options_places.lt](../conformance/expressions/fields_through_options_places.lt), [modes/inout_marking.lt](../conformance/modes/inout_marking.lt), [modes/self_modes.lt](../conformance/modes/self_modes.lt), [names/self_member_outside.lt](../conformance/names/self_member_outside.lt), [names/self_outside_method.lt](../conformance/names/self_outside_method.lt), [ported/temperature_conversion.lt](../conformance/ported/temperature_conversion.lt), [program/doc_example_errors.lt](../conformance/program/doc_example_errors.lt), [traits/self_and_big_self.lt](../conformance/traits/self_and_big_self.lt), [values/inout_self_on_raise.lt](../conformance/values/inout_self_on_raise.lt), [values/receiver_read_panics.lt](../conformance/values/receiver_read_panics.lt).

<a id="traits.associated-functions"></a>
A function of an `impl` block without `self` is an **associated function**, called as `Type.f(…)`, as in `Map.with_default(0.0)`. A constant of the block is read as `Type.NAME`, as in `f64.PI` ([declarations.constant-declarations](10-declarations.md#declarations.constant-declarations)). Neither is reached as a method: `x.f(…)` for an associated function `f` is E0314, *no such method or member* ([traits.method-resolution](#traits.method-resolution)).

Tests: [traits/associated_generic_function.lt](../conformance/traits/associated_generic_function.lt), [traits/inherent_methods.lt](../conformance/traits/inherent_methods.lt), [traits/method_resolution.lt](../conformance/traits/method_resolution.lt).

<a id="traits.inherent-names"></a>
A name is defined at most once across all the inherent blocks of a type, bounded or not. A function of a block can't declare a generic with the name of one of the block's generics. Either mistake is E0208, *name defined twice* ([declarations.unique-names](10-declarations.md#declarations.unique-names)).

Tests: [checking/method_declared_twice.lt](../conformance/checking/method_declared_twice.lt), [names/generics_reused.lt](../conformance/names/generics_reused.lt), [traits/method_generics.lt](../conformance/traits/method_generics.lt), [traits/unique_inherent_names.lt](../conformance/traits/unique_inherent_names.lt).

<a id="traits.bounded-blocks"></a>
A block may bound its type's parameters, as in `impl<T: Ord> List<T> { fn sorted(self) -> List<T> { … } }`. Its functions exist only for the type arguments that meet the bounds. Calling one on any other type is E0318, *unsatisfied bound*, which names the missing bound.

Tests: [traits/bounded_block.lt](../conformance/traits/bounded_block.lt).

## Traits

<a id="traits.declaring-trait"></a>
`trait Name { … }` declares a **trait**: a set of function signatures, each with an optional default body. A function whose first parameter is `self` or `inout self` is a method of the trait, and a method may be generic. A trait whose functions are all methods, with no parameters of its own, abstracts over `Self` alone, and is part of core. A trait's parameters, its functions without `self`, its constants and constructor traits are part of the advanced tier ([traits.advanced-tier](#traits.advanced-tier)).

Tests: [lexical/bodiless_signatures.lt](../conformance/lexical/bodiless_signatures.lt), [reflection/trait_parameter_name.lt](../conformance/reflection/trait_parameter_name.lt), [traits/default_methods.lt](../conformance/traits/default_methods.lt), [traits/method_generics.lt](../conformance/traits/method_generics.lt), [traits/user_impls_override.lt](../conformance/traits/user_impls_override.lt).

<a id="traits.implementing-trait"></a>
`impl<A: Bound, …> Trait for Con<A, …> { … }` implements a trait for a type constructor. The arguments of `Con` must be the impl's parameters, each once, in any order, as for an inherent block, or the impl is E0302, *invalid impl type*. The impl's parameters may carry bounds. The arguments of a type must meet them for the impl's methods to apply to it ([traits.method-resolution](#traits.method-resolution)). So `impl<T: Show> Describe for List<T>` implements `Describe` for every list whose elements can be shown.

Tests: [traits/impl_bounds.lt](../conformance/traits/impl_bounds.lt), [traits/trait_impl_type.lt](../conformance/traits/trait_impl_type.lt), [traits/user_impls_override.lt](../conformance/traits/user_impls_override.lt).

<a id="traits.impl-members"></a>
A trait impl holds a member for each function and constant of the trait that has no default. It may leave out those that have one, whose default then applies. A member that it lacks is E0305, *missing trait member*, at the impl. It holds no other member: one that the trait doesn't declare is E0306, *member not in the trait*, at its name. Its members take no `pub`, and are visible wherever both the trait and the type are ([program.visibility](04-programs.md#program.visibility)).

Tests: [checking/trait_broken_before_its_block.lt](../conformance/checking/trait_broken_before_its_block.lt), [parameters/const_not_in_trait.lt](../conformance/parameters/const_not_in_trait.lt), [program/missing_method_reached.lt](../conformance/program/missing_method_reached.lt), [traits/default_methods.lt](../conformance/traits/default_methods.lt), [traits/impl_methods.lt](../conformance/traits/impl_methods.lt).

<a id="traits.impl-signatures"></a>
Each member of a trait impl has the signature that the trait declares, with `Self` replaced by the impl's type. Each trait parameter is replaced by its argument ([traits.trait-arguments](#traits.trait-arguments)). So the member has the same parameter modes and types, the same parameters written `escaping`, and the same return type and row as the trait's declaration. Its result is written `inout` where the trait's is ([projections.declaring-projection](13-modes.md#projections.declaring-projection)).

The member's generics correspond to those of the trait function in order, with the same bounds, and may have other names. A member whose signature differs is E0307, *method signature differs from the trait's*, at its name. A trait method's non-escaping parameters pass their arguments' effects through, as a function's do ([effects.non-escaping-parameters](12-effects.md#effects.non-escaping-parameters)). So the method of every impl passes them through alike, and so does a call through a bound.

Tests: [traits/escaping_mismatch.lt](../conformance/traits/escaping_mismatch.lt), [traits/impl_methods.lt](../conformance/traits/impl_methods.lt), [traits/impl_signatures.lt](../conformance/traits/impl_signatures.lt), [traits/non_escaping_method.lt](../conformance/traits/non_escaping_method.lt).

<a id="traits.coherence"></a>
A trait has at most one impl per type constructor. A second impl is E0304, *overlapping impls*, at the later impl. An impl covers a whole constructor, so no impl for `List<str>` stands beside one for every `List<T>`.

Tests: [traits/overlapping_impls.lt](../conformance/traits/overlapping_impls.lt).

<a id="traits.orphan-rule"></a>
An impl must be in its trait's module or in its type's module. An impl anywhere else is an **orphan impl**, which is E0303. So no module can give `f64` an impl of `Hash`, because both are declared in `std.prelude`.

Tests: [traits/foreign_impls.lt](../conformance/traits/foreign_impls.lt), [traits/orphan_impl](../conformance/traits/orphan_impl/).

## Bounds

<a id="traits.bounds"></a>
A **bound** limits a type parameter to the types that implement one or more traits. It is written after the parameter, with `+` between traits, as `<T: Ord + Show>`. Bounds stand among the generics of a function or an impl, and in a `where` clause on a member type ([traits.where](#traits.where)). A bound test may also stand as the condition of an `if` ([meta.bound-tests](16-meta.md#meta.bound-tests)).

A type's parameters and a trait's take no bounds, and a trait requires no other trait. So `type Sorted<T: Ord> = …` and `trait Sorted: Ord { … }` are E0100, *syntax error*. A bound names a trait, or a record's fields ([records.record-bounds](07-types.md#records.record-bounds)). A name of another kind there, as a type in `<T: Point>`, is E0212, *wrong kind of name*.

Tests: [declarations/bound_on_type.lt](../conformance/declarations/bound_on_type.lt), [names/wrong_kind.lt](../conformance/names/wrong_kind.lt), [traits/bound_on_trait.lt](../conformance/traits/bound_on_trait.lt).

<a id="traits.unsatisfied-bounds"></a>
Inside a function, a type parameter's bounds are all that is known of its type. The methods of their traits, and the operators that those traits stand behind ([traits.operators](#traits.operators)), apply to its values. Where a type parameter is given a type, as at a call, the type must meet each of its bounds. A method's receiver must meet the bounds of the impl or the block that holds the method ([traits.bounded-blocks](#traits.bounded-blocks)).

A use that needs an impl that a type lacks is E0318, *unsatisfied bound*, at the use, and the diagnostic names the type and the trait. So `a == b` on a type parameter without `Eq` is E0318, and so is `m[k]` on a `Map<K, V>` whose `K` lacks the bound `Eq + Hash`.

Tests: [reflection/shapes_have_no_impls.lt](../conformance/reflection/shapes_have_no_impls.lt), [std/map_generic_key_bounded.lt](../conformance/std/map_generic_key_bounded.lt), [std/map_generic_key_unbounded.lt](../conformance/std/map_generic_key_unbounded.lt), [traits/bound_argument_left_open.lt](../conformance/traits/bound_argument_left_open.lt), [traits/bounds.lt](../conformance/traits/bounds.lt), [traits/required_traits.lt](../conformance/traits/required_traits.lt).

<a id="traits.bound-reported-once"></a>
A body reports one E0318 for each type and trait it lacks, at the first use, in source order, that needs it. The traits that a use needs are those the use itself requires, not those that an impl with a bound would require in turn. So `a[1.0]` on `a: Map<f64, str>` lacks `Hash` for `f64`, while `a == b` lacks `Eq` for `Map<f64, str>`, and a body with both reports two. And `var m = Map.new()` followed by `m[k] = 1`, where the type of `k` has no `Hash`, reports one E0318, at `Map.new()`.

Tests: [std/map_new_float_key.lt](../conformance/std/map_new_float_key.lt), [traits/bound_reported_once.lt](../conformance/traits/bound_reported_once.lt), [traits/bounds_of_conditional_impl.lt](../conformance/traits/bounds_of_conditional_impl.lt).

## Method resolution

<a id="traits.method-resolution"></a>
In a method call `recv.m(args)`, the receiver's type must be known where the call stands ([types.known-types](07-types.md#types.known-types)). Otherwise the call is E0312, *type that can't be inferred*, which asks for an annotation. With `C` the head constructor of that type, as `List` is for a `List<str>`, `m` is looked up in this order:

1. An inherent function `m` of `C`. If it takes no `self`, the call is E0314, which shows the form `C.m(…)`.
2. Otherwise, a method `m` of a trait in scope ([traits.traits-in-scope](#traits.traits-in-scope)) that has an impl for `C`. If the impl has bounds that the receiver's type arguments don't meet, the call is E0318, which names the missing bound.
3. For a receiver whose type is a type parameter, or is headed by a constructor parameter ([traits.constructor-parameters](#traits.constructor-parameters)), the methods of the traits of its bounds.
4. Otherwise, a field `m` of the record type, or the element `m` of the tuple type, as in `pair.0(x)`. Its type must be a function type, or the call is E0311, *mismatched types*. The call calls its value. Parentheses only group, so `(r.m)(x)` means `r.m(x)`.

When none of these finds `m`, the call is E0314, *no such method or member*.

Tests: [expressions/closure_inout_in_list.lt](../conformance/expressions/closure_inout_in_list.lt), [expressions/field_access.lt](../conformance/expressions/field_access.lt), [expressions/unknown_types_at_use.lt](../conformance/expressions/unknown_types_at_use.lt), [std/option_filter_rejected.lt](../conformance/std/option_filter_rejected.lt), [traits/default_methods.lt](../conformance/traits/default_methods.lt), [traits/field_vs_trait.lt](../conformance/traits/field_vs_trait.lt), [traits/impl_bounds.lt](../conformance/traits/impl_bounds.lt), [traits/method_resolution.lt](../conformance/traits/method_resolution.lt), [traits/structural_impls.lt](../conformance/traits/structural_impls.lt), [traits/tuple_elements.lt](../conformance/traits/tuple_elements.lt), [types/error_type_cascades.lt](../conformance/types/error_type_cascades.lt), [types/unknown_receiver.lt](../conformance/types/unknown_receiver.lt).

<a id="traits.traits-in-scope"></a>
For a method call, a trait is in scope when it is declared in one of these modules:

- the current module
- the prelude
- a module that one of the current module's `use` declarations names

A trait reached only through a parent module isn't in scope. So after `use shapes`, a trait of `shapes.solid` is in scope only once `use shapes.solid` is written. The call also needs the impl's method to be visible, which it is wherever both the trait and the type are ([program.visibility](04-programs.md#program.visibility)).

Tests: [traits/trait_through_parent](../conformance/traits/trait_through_parent/), [traits/trait_through_use](../conformance/traits/trait_through_use/), [traits/trait_visibility](../conformance/traits/trait_visibility/).

<a id="traits.ambiguous-methods"></a>
When methods of several traits in scope match a call, the call is E0319, *ambiguous method*. The fix is the qualified form, which names the trait ([traits.qualified-calls](#traits.qualified-calls)).

Tests: [traits/method_resolution.lt](../conformance/traits/method_resolution.lt), [traits/no_overloading.lt](../conformance/traits/no_overloading.lt).

<a id="traits.name-clashes"></a>
A type can't have an inherent function with the name of a function or a constant of a trait it implements. This holds whether the type implements the trait through an impl that the program writes or through a structural impl ([traits.structural-impls](#traits.structural-impls)). The two are E0308, *inherent method hides a trait method*. Here a generic type counts as implementing a structural trait when it would implement it with every type parameter implementing it. So a record with an inherent `show` is E0308, unless the type of one of its fields can't be shown, as a function type can't.

Tests: [traits/generic_structural_clash.lt](../conformance/traits/generic_structural_clash.lt), [traits/inherent_hides_trait_method.lt](../conformance/traits/inherent_hides_trait_method.lt).

<a id="traits.qualified-calls"></a>
`Trait.m(x, …)` and `Type.m(x, …)` are always available. `Type.m` finds `m` as steps 1 and 2 of [traits.method-resolution](#traits.method-resolution) find it for the head constructor of `Type`, whether or not `m` takes `self`. The receiver is then the first argument, so an `inout self` receiver is an `inout` argument, marked at the call ([expressions.inout-arguments](08-expressions.md#expressions.inout-arguments)).

`Trait.m` and `Type.m` are also function values, whose first parameter is the receiver, as in `xs.map(Counter.get)` and `xs.map(Show.show)`. Their types are instantiated where they are used, as the types of a generic function are ([types.no-type-arguments](07-types.md#types.no-type-arguments)).

Tests: [ported/binary_search.lt](../conformance/ported/binary_search.lt), [program/prelude_other_namespace.lt](../conformance/program/prelude_other_namespace.lt), [traits/default_methods.lt](../conformance/traits/default_methods.lt), [traits/method_resolution.lt](../conformance/traits/method_resolution.lt), [traits/no_overloading.lt](../conformance/traits/no_overloading.lt), [traits/one_home_per_type.lt](../conformance/traits/one_home_per_type.lt), [traits/qualified_calls.lt](../conformance/traits/qualified_calls.lt), [traits/qualified_names_as_values.lt](../conformance/traits/qualified_names_as_values.lt).

<a id="traits.no-overloading"></a>
Resolution never looks at the types of the arguments, only at the type of the receiver. Each method has exactly one home for each type. So a call never chooses among candidates by its arguments: there is no overloading.

Tests: [traits/no_overloading.lt](../conformance/traits/no_overloading.lt), [traits/one_home_per_type.lt](../conformance/traits/one_home_per_type.lt).

## The prelude traits

<a id="traits.prelude-traits"></a>
`std.prelude` declares four traits:

```stilt
pub trait Eq { fn eq(self, other: Self) -> bool }
pub trait Ord { fn compare(self, other: Self) -> Ordering }
pub trait Hash { fn hash(self) -> u64 }
pub trait Show {
  fn show(self) -> str
  fn show_nested(self) -> str { self.show() }
}
```

The value that `hash` returns is unspecified, except that equal values have equal hashes within one run. Programs can't observe it through maps, which iterate in insertion order ([std.maps](17-std.md#std.maps)).

Tests: [traits/structural_eq_ord_hash.lt](../conformance/traits/structural_eq_ord_hash.lt), [traits/user_impls_override.lt](../conformance/traits/user_impls_override.lt).

<a id="traits.operators"></a>
`a == b` means `Eq.eq(a, b)`, and `a != b` means its negation. On every type but the numeric types, `a < b` means `Ord.compare(a, b) == Less`, and `<=`, `>` and `>=` are defined the same way. On the numeric types, the operators are primitive ([numbers.comparisons](06-numbers.md#numbers.comparisons)). A type parameter isn't a numeric type, even where a float instantiates it, so generic code orders floats with `compare` ([traits.floats](#traits.floats)). An operator defined through a trait calls the impl's method, and has its implicit effects ([facts.inference](15-facts.md#facts.inference)).

Tests: [effects/without_panic_traits](../conformance/effects/without_panic_traits/), [implicit/traits](../conformance/implicit/traits/), [traits/float_order.lt](../conformance/traits/float_order.lt), [traits/generic_float_order.lt](../conformance/traits/generic_float_order.lt), [traits/operators_use_impls.lt](../conformance/traits/operators_use_impls.lt), [types/comparison_mismatch_first.lt](../conformance/types/comparison_mismatch_first.lt).

<a id="traits.required-traits"></a>
Each use in this table requires a trait of the types it is used on, and a type without the impl is E0318, *unsatisfied bound* ([traits.unsatisfied-bounds](#traits.unsatisfied-bounds)):

| Use | Requires |
| --- | --- |
| `==`, `!=` | `Eq` |
| `<`, `<=`, `>`, `>=` | `Ord` |
| Map keys ([std.map-key-bounds](17-std.md#std.map-key-bounds)) | `Eq + Hash` |
| Interpolation | `Show` |

Tests: [traits/bound_reported_once.lt](../conformance/traits/bound_reported_once.lt), [traits/function_values_not_comparable.lt](../conformance/traits/function_values_not_comparable.lt), [traits/missing_impls.lt](../conformance/traits/missing_impls.lt), [traits/required_traits.lt](../conformance/traits/required_traits.lt).

<a id="traits.built-in-impls"></a>
The integer types, `bool`, `str` and `()` implement `Eq`, `Ord`, `Hash` and `Show`. `f32` and `f64` implement `Eq`, `Ord` and `Show` ([traits.floats](#traits.floats)). `Never` implements all four, though none of their methods can ever be called. Function types implement none, so a function can't be compared, be a map key or be shown. `str` is ordered by its bytes, which is the same as ordering by Unicode scalar value, and `false < true`.

Tests: [traits/function_values_not_comparable.lt](../conformance/traits/function_values_not_comparable.lt), [traits/never_impls.lt](../conformance/traits/never_impls.lt), [traits/unit_impls.lt](../conformance/traits/unit_impls.lt).

## Structural impls

<a id="traits.structural-impls"></a>
Tuples, records, variant types, `List`, `Option` and `Result` implement all four prelude traits automatically, whenever the type of every component implements them. So `Option<T>` implements `Eq` when `T` does. `Map` implements `Eq` and `Show` the same way, and neither `Ord` nor `Hash` ([traits.map-equality](#traits.map-equality)). Anonymous records ([records.field-order](07-types.md#records.field-order)) and arrays ([generics.array-traits](07-types.md#generics.array-traits)) have these impls too. These automatic impls are the **structural impls**. An impl that the program writes in the type's home module replaces the structural one.

Tests: [ported/word_frequency.lt](../conformance/ported/word_frequency.lt), [procedural/numbers](../conformance/procedural/numbers/), [std/map_keeps_stored_key.lt](../conformance/std/map_keeps_stored_key.lt), [std/set_functions.lt](../conformance/std/set_functions.lt), [std/show_every_type.lt](../conformance/std/show_every_type.lt), [std/structural_keys.lt](../conformance/std/structural_keys.lt), [traits/missing_impls.lt](../conformance/traits/missing_impls.lt), [traits/nested_impls_shown.lt](../conformance/traits/nested_impls_shown.lt), [traits/operators_use_impls.lt](../conformance/traits/operators_use_impls.lt), [traits/structural_eq_ord_hash.lt](../conformance/traits/structural_eq_ord_hash.lt), [traits/structural_impls.lt](../conformance/traits/structural_impls.lt), [traits/structural_show.lt](../conformance/traits/structural_show.lt), [traits/user_impls_override.lt](../conformance/traits/user_impls_override.lt).

<a id="traits.structural-calls"></a>
The structural impls work through the components from first to last, so the calls they make to the impls of the components are fixed:

- Equality compares components with `eq` and stops at the first unequal pair. Different variants, and lists of different lengths, are unequal without comparing any component.
- Order is lexicographic, comparing components with `compare` until a pair differs. A list that runs out first, with no pair differing, is the lesser, so `[1, 2] < [1, 2, 0]`. Records compare their fields in declaration order. Variants compare first by their order in the type's declaration, then by payload, so `None < Some(0)` and `Ok(1) < Err(0)` ([std.option-result-and-ordering](17-std.md#std.option-result-and-ordering)).
- Hashing calls `hash` on every component.

Tests: [std/lists.lt](../conformance/std/lists.lt), [std/option_and_result.lt](../conformance/std/option_and_result.lt), [std/sorting.lt](../conformance/std/sorting.lt), [traits/structural_calls.lt](../conformance/traits/structural_calls.lt), [traits/structural_eq_ord_hash.lt](../conformance/traits/structural_eq_ord_hash.lt), [traits/structural_eq_reaches_component.lt](../conformance/traits/structural_eq_reaches_component.lt), [traits/structural_hash_reaches_component.lt](../conformance/traits/structural_hash_reaches_component.lt), [traits/structural_order_reaches_component.lt](../conformance/traits/structural_order_reaches_component.lt).

<a id="traits.map-equality"></a>
Two maps are equal when they hold the same entries, in any order. Maps of different lengths are unequal. Otherwise equality finds each key of the first map, in insertion order, in the second ([std.finding-keys](17-std.md#std.finding-keys)), and compares the two values with `eq`, stopping at the first difference. Finding a key needs the `Hash` of its type, so `Map<K, V>` implements `Eq` only when `K` implements `Hash` too. A map's default takes no part in its equality or in its `Show`.

Tests: [std/map_defaults.lt](../conformance/std/map_defaults.lt), [std/map_float_key_equality.lt](../conformance/std/map_float_key_equality.lt), [std/maps.lt](../conformance/std/maps.lt), [traits/map_equality.lt](../conformance/traits/map_equality.lt).

<a id="traits.hash-follows-written-eq"></a>
A type whose `Eq` impl the program writes gets no structural `Hash`. It implements `Hash` only once the program writes that impl too, and until then it can't be a map key (E0318, *unsatisfied bound*). Keeping the hashes of equal values equal is then the program's task.

Some map operations depend on which stored keys they compare with `eq`, which depends on which keys share a hash. The outcome of such an operation is unspecified when written impls break that law, or when the `eq` of a key type can panic.

Tests: [traits/written_eq_with_hash.lt](../conformance/traits/written_eq_with_hash.lt), [traits/written_eq_without_hash.lt](../conformance/traits/written_eq_without_hash.lt).

## Floats

<a id="traits.floats"></a>
`==` and `<` on floats follow IEEE 754 ([numbers.ieee-754](06-numbers.md#numbers.ieee-754)), and `Eq.eq` agrees with `==`. `Ord.compare` on floats is a total order. It follows the IEEE 754 totalOrder for every value but NaN, so `-0.0` is less than `0.0`. Every NaN, whatever its sign and payload, is equal to every other NaN and greater than every other value, `inf` included.

Everything that goes through `compare` uses this order: sorting, `<` in generic code and comparisons of compound values. So `(-0.0,) < (0.0,)` is true and `[f64.NAN] < [1.0]` is false. Floats don't implement `Hash`, so they can't be map keys (E0318, *unsatisfied bound*).

Tests: [std/sorting.lt](../conformance/std/sorting.lt), [traits/float_order.lt](../conformance/traits/float_order.lt), [traits/generic_float_order.lt](../conformance/traits/generic_float_order.lt), [traits/missing_impls.lt](../conformance/traits/missing_impls.lt), [traits/required_traits.lt](../conformance/traits/required_traits.lt).

## Showing values

<a id="traits.show"></a>
For `str`, `show` returns the text unchanged, while `show_nested` returns it quoted and escaped. Containers call `show_nested` on their elements, and interpolation calls `show`. So `"{s}"` writes `ana`, while `"{xs}"` writes `["ana", "bo"]`. [std.show-output](17-std.md#std.show-output) gives the exact output of every type.

Tests: [std/show.lt](../conformance/std/show.lt), [std/show_every_type.lt](../conformance/std/show_every_type.lt), [traits/nested_impls_shown.lt](../conformance/traits/nested_impls_shown.lt), [traits/structural_show.lt](../conformance/traits/structural_show.lt), [traits/user_impls_override.lt](../conformance/traits/user_impls_override.lt), [values/string_appends.lt](../conformance/values/string_appends.lt).

## Trait parameters

<a id="traits.trait-parameters"></a>
`trait Name<P, …> { … }` declares a trait with **trait parameters**. They are uppercase names with no bounds, and each names a type throughout the trait's members, where it is written by its name alone. A trait parameter is never a value parameter or a pack ([generics.value-parameter-positions](07-types.md#generics.value-parameter-positions), [variadics.packs](07-types.md#variadics.packs)). A function of the trait can't declare a generic with the name of a trait parameter. That is E0208, *name defined twice*, as it is in an inherent block ([traits.inherent-names](#traits.inherent-names)). Trait parameters are part of the advanced tier ([traits.advanced-tier](#traits.advanced-tier)).

Tests: [parameters/collections.lt](../conformance/parameters/collections.lt), [parameters/impls.lt](../conformance/parameters/impls.lt), [reflection/trait_parameter_name.lt](../conformance/reflection/trait_parameter_name.lt).

<a id="traits.trait-arguments"></a>
An impl of such a trait, `impl<A, …> Name<T, …> for Con<A, …> { … }`, gives one type argument for each trait parameter. An argument is a type that may name the impl's parameters. The wrong number of arguments, or none, is E0300, *wrong number of type arguments*.

The trait still has at most one impl per type constructor ([traits.coherence](#traits.coherence)), so the impl's type fixes the arguments. `impl Convert<f64> for i64` beside `impl Convert<str> for i64` is E0304, *overlapping impls*. A trait and a type name one impl, as a path to its members does ([edits.paths](19-tools.md#edits.paths)). The impl's parameters are still the arguments of `Con`, each once, so `impl<T> Convert<T> for i64` is E0302, *invalid impl type*.

Tests: [parameters/collections.lt](../conformance/parameters/collections.lt), [parameters/impls.lt](../conformance/parameters/impls.lt), [reflection/trait_parameter_name.lt](../conformance/reflection/trait_parameter_name.lt).

<a id="traits.bound-arguments"></a>
A bound names a trait with all its arguments, as `C: Collection<i64>`, or with none, as `C: Collection`. A bound with some arguments but not all is E0300, *wrong number of type arguments*. An argument may be any type, including another generic of the same function. That generic is then inferred from the impl as any generic is, as in `fn total<C: Collection<T>, T: Show>(c: C)`. A type meets the bound when it has an impl of the trait whose arguments, instantiated for that type, are the bound's. Otherwise the use is E0318, *unsatisfied bound*, which names the bound and the argument that differs.

Tests: [checking/bound_on_a_broken_trait.lt](../conformance/checking/bound_on_a_broken_trait.lt), [parameters/collections.lt](../conformance/parameters/collections.lt), [parameters/impls.lt](../conformance/parameters/impls.lt), [parameters/member_types.lt](../conformance/parameters/member_types.lt), [polymorphism/argument_errors.lt](../conformance/polymorphism/argument_errors.lt), [traits/bound_argument_left_open.lt](../conformance/traits/bound_argument_left_open.lt).

<a id="traits.member-types"></a>
`C.Item` is a **member type** when `C` is a type parameter of the function or of its impl block, and `Item` is a parameter of the trait of a bound of `C`. It is the type that the impl of that trait for the type of `C` gives `Item`. Where the bound gives the argument, the member type is that argument, so under `C: Collection<i64>`, `C.Item` is `i64`.

A member type is E0334, *member type that names nothing*, when its `C` isn't a type parameter, or when no trait of the bounds of `C` has a parameter `Item`. A member type that the traits of two of the bounds have is E0335, *ambiguous member type*. Its fix names the argument with a generic of the function, as in `C: Collection<T>`. Member types are part of the advanced tier.

Tests: [parameters/collections.lt](../conformance/parameters/collections.lt), [parameters/member_types.lt](../conformance/parameters/member_types.lt), [parameters/where_clauses.lt](../conformance/parameters/where_clauses.lt), [parameters/where_on_a_missing_member.lt](../conformance/parameters/where_on_a_missing_member.lt).

<a id="traits.where"></a>
A `where` clause bounds member types, as in `where C.Item: Ord + Show, D.Key: Hash`. It stands in one of two places:

- after a function's signature, on the line where the signature ends and before its `without` clause ([syntax.limit-clauses](03-syntax.md#syntax.limit-clauses))
- after an impl's type, before its `{`

A function of an inherent block may bound the member types of the block's parameters. Each bound of a `where` clause is checked as a bound beside a parameter is. Where a bound's argument fixes the member type, as in `C: Collection<f64> where C.Item: Hash`, the fixed type must meet the bound, or the bound is E0318, *unsatisfied bound*.

Each of these is E0336, *`where` bound that isn't on a member type*:

- a bound in a `where` clause on anything but a member type, whose fix moves it beside its parameter
- a `where` clause on a function of a trait or of a trait impl, which has the trait's signature and can't bound what the trait leaves open

`where` is a keyword ([lexical.keywords](02-lexical.md#lexical.keywords)), and a `where` clause is part of the advanced tier.

Tests: [checking/bound_on_a_broken_trait.lt](../conformance/checking/bound_on_a_broken_trait.lt), [parameters/where_clauses.lt](../conformance/parameters/where_clauses.lt), [parameters/where_errors.lt](../conformance/parameters/where_errors.lt), [parameters/where_fixed.lt](../conformance/parameters/where_fixed.lt), [parameters/where_on_a_missing_member.lt](../conformance/parameters/where_on_a_missing_member.lt).

## Trait functions without `self` and trait constants

<a id="traits.functions-without-self"></a>
A trait may declare functions that take no `self`, and constants, `const NAME: T`. Each may have a default, `= expr`, or not, and an impl holds them as it holds methods ([traits.impl-members](#traits.impl-members)). They are named on a type:

- `T.empty()` and `T.ZERO` on a type parameter bounded by the trait
- `i64.empty()` and `i64.ZERO` on a type with an impl, found as [traits.qualified-calls](#traits.qualified-calls) finds `Type.m`
- `Self.empty()` in the trait's own members

`T.empty` is a function value, as `Type.m` is. `Trait.f(…)` for a function without `self`, and `Trait.NAME`, are E0330, *trait function or constant named without a type*, whose fix writes the type. No call is resolved from the type it is expected to have ([traits.no-overloading](#traits.no-overloading)). In a module that names `std.meta`, `T.shape()` and `T.name()` are found after these ([meta.shape-and-name](16-meta.md#meta.shape-and-name)). Trait functions without `self` and trait constants are part of the advanced tier.

Tests: [parameters/trait_function_errors.lt](../conformance/parameters/trait_function_errors.lt), [parameters/trait_functions.lt](../conformance/parameters/trait_functions.lt).

<a id="traits.trait-constants"></a>
A trait constant's type may name `Self` and the trait's parameters. It has one value for each impl, unlike a constant of a generic block ([declarations.impl-constants](10-declarations.md#declarations.impl-constants)). It is evaluated as the constants of a type are ([declarations.constant-evaluation](10-declarations.md#declarations.constant-evaluation)). Trait constants that refer to one another in a cycle are E0327, *constants in a cycle*.

Tests: [parameters/shared_names.lt](../conformance/parameters/shared_names.lt), [parameters/trait_function_errors.lt](../conformance/parameters/trait_function_errors.lt).

<a id="traits.shared-member-names"></a>
A type may implement two traits that each have a function or a constant of one name. Naming that member on the type, or on a type parameter whose bounds both have it, is E0319, *ambiguous method*, as for a method ([traits.ambiguous-methods](#traits.ambiguous-methods)). No form names it through one of the traits alone. An inherent function with the name of such a function or constant of a trait that the type implements is E0308, *inherent method hides a trait method* ([traits.name-clashes](#traits.name-clashes)).

Tests: [parameters/ambiguous_members.lt](../conformance/parameters/ambiguous_members.lt), [parameters/shared_names.lt](../conformance/parameters/shared_names.lt), [parameters/trait_function_errors.lt](../conformance/parameters/trait_function_errors.lt).

## Constructor traits

<a id="traits.constructor-traits"></a>
A trait whose members write `Self` applied to type arguments, as `Self<A>`, is a **constructor trait**. It abstracts over a type constructor that takes that many type arguments, its **arity**. Each `Self` in it takes the same number of arguments, so `Self` alone, or with another number of them, is E0337, *type of the wrong kind*. Constructor traits are part of the advanced tier.

Tests: [parameters/constructor_errors.lt](../conformance/parameters/constructor_errors.lt), [parameters/constructors.lt](../conformance/parameters/constructors.lt).

<a id="traits.receiver-types"></a>
Each method of a constructor trait writes the type of its receiver, as `self: Self<A>` or `inout self: Self<A>`, and that type is `Self` applied to types. A method of an impl writes it with the impl's constructor, as `self: Option<A>` ([traits.constructor-impls](#traits.constructor-impls)). Each of these is E0338, *receiver's type written or missing*:

- a method of a constructor trait whose receiver's type isn't written
- a receiver with a written type anywhere but in a constructor trait and its impls

Tests: [parameters/constructor_errors.lt](../conformance/parameters/constructor_errors.lt), [parameters/inherent_receiver_type.lt](../conformance/parameters/inherent_receiver_type.lt).

<a id="traits.constructor-impls"></a>
`impl Name for Con { … }` implements a constructor trait for a type constructor of the trait's arity. The impl writes `Con` without arguments and has no impl parameters, as in `impl Mappable for Option`. Each of these is E0337, *type of the wrong kind*, and the members of such an impl aren't checked:

- a constructor of another arity, as `Map` for a trait over `Self<A>`
- an applied type, as `List<i64>`
- a tuple or a function type

Coherence (E0304) and the orphan rule (E0303) apply as to any trait. The impl's members have the trait's signatures, with each `Self<…>` replaced by `Con<…>` (E0307), and their non-escaping parameters pass their arguments' effects through ([traits.impl-signatures](#traits.impl-signatures)). A constructor trait has no structural impls.

Tests: [parameters/constructor_errors.lt](../conformance/parameters/constructor_errors.lt), [parameters/constructors.lt](../conformance/parameters/constructors.lt).

<a id="traits.constructor-parameters"></a>
A generic of a function bounded by a constructor trait is a **constructor parameter**, of the arity of that trait: under `F: Mappable`, `F<i64>` is a type. Each of these is E0337, *type of the wrong kind*:

- a constructor parameter written without its arguments or with another number of them
- a bound list that mixes a constructor trait with another trait, or two constructor traits of different arities
- a constructor trait bounding a generic of an impl block

At a call, a constructor parameter is inferred from the head of the argument's type, so `doubled(Some(2))` takes `F` to be `Option`. A type whose head has no impl of the trait, as a tuple, is E0318, *unsatisfied bound*. A type that isn't headed by a constructor applied to that many arguments, as `i64` where `F<i64>` is expected, is E0311, *mismatched types*. A method call whose receiver's type is headed by a constructor parameter finds the methods of its bounds ([traits.method-resolution](#traits.method-resolution)).

Tests: [parameters/constructor_errors.lt](../conformance/parameters/constructor_errors.lt), [parameters/constructors.lt](../conformance/parameters/constructors.lt), [parameters/constructors_several.lt](../conformance/parameters/constructors_several.lt).

<a id="traits.advanced-tier"></a>
A module is in the advanced tier ([program.module-tier](04-programs.md#program.module-tier)) when it does any of these:

- declares a trait with parameters, a trait function without `self`, a trait constant or a constructor trait
- writes an impl of such a trait, or names one in a bound
- writes a member type or a `where` clause

A module that only calls the methods of such a trait stays in core.

Checked by: the facts suite, whose `tests/facts/parameters.lt` carries `//~ tier: advanced`, which `just facts` checks, and the toolchain's tests of `stilt show` (`compiler/stilt-cli/tests/show.rs`).
