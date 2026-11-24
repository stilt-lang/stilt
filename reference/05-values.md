# 5. The value model

This chapter says what a value is and how it moves through a program. It gives copies, the bindings that may change, strings, what passing a value to a function does to the caller's variable, and the order in which expressions are evaluated. [Expressions](08-expressions.md) defines places and assignment, and [Modes and exclusivity](13-modes.md) defines `inout` and the law of exclusivity.

## Value semantics

<a id="values.value-semantics"></a>
Every core value has **value semantics**. A value can appear to change only through a binding the program names as mutable: a `var` binding or an `inout` parameter ([modes.what-can-be-modified](13-modes.md#modes.what-can-be-modified)).

Tests: [values/independent_copies.lt](../conformance/values/independent_copies.lt), [values/let_immutable.lt](../conformance/values/let_immutable.lt).

<a id="values.independent-copies"></a>
Each of these makes a copy that is independent of the original:

- assigning a value;
- passing it as a `let` argument;
- binding it in a pattern ([patterns.bindings-are-copies](09-patterns.md#patterns.bindings-are-copies));
- capturing it in a closure ([expressions.capture](08-expressions.md#expressions.capture)).

A change to the copy never shows through the original, and a change to the original never shows through the copy. There are no move errors and no `Copy` trait.

Tests: [expressions/closure_captures_at_creation.lt](../conformance/expressions/closure_captures_at_creation.lt), [modes/read_before_call.lt](../conformance/modes/read_before_call.lt), [patterns/bindings_are_copies.lt](../conformance/patterns/bindings_are_copies.lt), [ported/hylo_geometry.lt](../conformance/ported/hylo_geometry.lt), [ported/hylo_synthetic_copy.lt](../conformance/ported/hylo_synthetic_copy.lt), [ported/levenshtein.lt](../conformance/ported/levenshtein.lt), [ported/swift_arrays.lt](../conformance/ported/swift_arrays.lt), [values/argument_copies.lt](../conformance/values/argument_copies.lt), [values/closure_copies.lt](../conformance/values/closure_copies.lt), [values/copy_on_write.lt](../conformance/values/copy_on_write.lt), [values/generic_copies.lt](../conformance/values/generic_copies.lt), [values/independent_copies.lt](../conformance/values/independent_copies.lt), [values/no_copy_trait.lt](../conformance/values/no_copy_trait.lt), [values/string_appends.lt](../conformance/values/string_appends.lt), [values/strings.lt](../conformance/values/strings.lt).

<a id="values.let-and-var"></a>
`let` bindings are immutable. `var` bindings are mutable, and every part of a `var` can be assigned through a place ([expressions.assignment](08-expressions.md#expressions.assignment)), as in `p.x = 1` or `xs[i] = v`. Assigning to a `let` binding or to any part of it, or calling a method that takes `inout self` on it, is E0403, *modifying what can't be modified* ([modes.what-can-be-modified](13-modes.md#modes.what-can-be-modified)).

Tests: [modes/read_only_bindings.lt](../conformance/modes/read_only_bindings.lt), [modes/var_patterns.lt](../conformance/modes/var_patterns.lt), [ported/hylo_synthetic_copy.lt](../conformance/ported/hylo_synthetic_copy.lt), [ported/look_and_say.lt](../conformance/ported/look_and_say.lt), [values/let_immutable.lt](../conformance/values/let_immutable.lt), [values/var_parts.lt](../conformance/values/var_parts.lt).

<a id="values.strings"></a>
`str` is an owned, immutable sequence of UTF-8 bytes, compared by content. No part of a string can be assigned, and no method changes one: a new string is made instead. No tier has first-class references or lifetimes. A view into a string is a view of the advanced tier ([views.std-view](13-modes.md#views.std-view)), and can't escape the function that holds the string.

Tests: [expressions/string_building.lt](../conformance/expressions/string_building.lt), [values/string_appends.lt](../conformance/values/string_appends.lt), [values/strings.lt](../conformance/values/strings.lt), [values/strings_immutable.lt](../conformance/values/strings_immutable.lt).

<a id="values.shared"></a>
`Shared<T>` belongs to the advanced tier. It is the only way to share mutable state with a common identity: a change made through one handle is visible through all of them ([shared.std-sync](14-tasks.md#shared.std-sync)). It is declared in `std.sync`, not in the prelude: a module that doesn't import `std.sync` can't name it.

Tests: [values/shared_is_advanced.lt](../conformance/values/shared_is_advanced.lt).

## Passing values

<a id="values.passing-values"></a>
Passing a value as a `let` argument, or as the receiver of a method that takes `self`, never changes the caller's variable. The callee gets an independent copy ([values.independent-copies](#values.independent-copies)), whatever it does with it. The caller may keep using the variable it passed, all of it or any part of it, on every path. It may use it after the call, in a later argument of the same call, in a later iteration of a loop or in a closure. This holds whether or not the callee consumes the parameter ([values.consumed-parameters](#values.consumed-parameters)).

Tests: [modes/bound_in_loops.lt](../conformance/modes/bound_in_loops.lt), [modes/consumed_and_inout.lt](../conformance/modes/consumed_and_inout.lt), [modes/consumed_inside_iteration.lt](../conformance/modes/consumed_inside_iteration.lt), [modes/consumed_with_inout_receiver.lt](../conformance/modes/consumed_with_inout_receiver.lt), [modes/used_after_passing.lt](../conformance/modes/used_after_passing.lt), [ported/swift_arrays.lt](../conformance/ported/swift_arrays.lt), [values/argument_copies.lt](../conformance/values/argument_copies.lt), [values/passed_in_branches.lt](../conformance/values/passed_in_branches.lt), [values/passed_in_loops.lt](../conformance/values/passed_in_loops.lt), [values/passed_in_while_head.lt](../conformance/values/passed_in_while_head.lt), [values/passed_inout_parameter.lt](../conformance/values/passed_inout_parameter.lt), [values/passed_on_raise_paths.lt](../conformance/values/passed_on_raise_paths.lt), [values/passed_overlapping_places.lt](../conformance/values/passed_overlapping_places.lt), [values/passed_receiver.lt](../conformance/values/passed_receiver.lt), [values/passed_temporaries.lt](../conformance/values/passed_temporaries.lt), [values/passed_then_assigned.lt](../conformance/values/passed_then_assigned.lt), [values/passed_then_captured.lt](../conformance/values/passed_then_captured.lt), [values/passed_then_reassigned.lt](../conformance/values/passed_then_reassigned.lt).

<a id="values.consumed-parameters"></a>
A function **consumes** a parameter when its body does one of these with it:

- returns it;
- stores it in a value;
- rebinds it with `var`;
- passes it to a parameter that its callee consumes;
- takes it apart to build in its place.

Only a parameter whose value is of a recursive type ([facts.allocation](15-facts.md#facts.allocation)) can be taken apart to build in its place. A body does this when a `match` or an `if let` on the parameter itself has an arm with both of these:

- a pattern that is a variant with a payload, or that has an alternative that is one;
- a body that builds a value of a variant of the same type with a payload, outside the closure literals it holds.

The compiler infers which parameters each function consumes, and the tools show it, as they show implicit effects. Like implicit effects, this fact is kept apart from the signatures that type checking reads, so editing a body never checks its callers again ([facts.interfaces](15-facts.md#facts.interfaces)). If a caller passes its last use of a value to a consumed parameter, the callee may reuse that memory in place. If the caller keeps using the place, the reuse is lost, and the tools show this at the call. Which parameters a function consumes changes nothing that a program can observe.

Tests: [modes/consumed_copies.lt](../conformance/modes/consumed_copies.lt), [modes/copies_stored_in_inout_arguments.lt](../conformance/modes/copies_stored_in_inout_arguments.lt).

Checked by: the compiler's tests of consumption (`compiler/stilt-cli/tests/consumption.rs` and `compiler/stilt-rc/src/consume/tests.rs`) and of building in a value's memory (`compiler/stilt-rc/src/reuse/tests.rs`), and the facts suite, whose `tests/facts/consumption.lt` gives `CONSUMES` at each kind of use, which `just facts` checks; the conformance tests of [values.passing-values](#values.passing-values) check that the caller's variable never changes.

<a id="values.inout-arguments"></a>
An `inout` argument holds every change the callee made: when the callee returns, when it raises, and when a handler ends its call ([handlers.call-that-handler-ends](12-effects.md#handlers.call-that-handler-ends)). Nothing is rolled back. A panic ends the process, so nothing can observe an `inout` argument after one.

Tests: [expressions/closure_inout_raise.lt](../conformance/expressions/closure_inout_raise.lt), [modes/consumed_and_inout.lt](../conformance/modes/consumed_and_inout.lt), [polymorphism/inout_past_caps.lt](../conformance/polymorphism/inout_past_caps.lt), [ported/hanoi.lt](../conformance/ported/hanoi.lt), [ported/hylo_local_inout.lt](../conformance/ported/hylo_local_inout.lt), [ported/insertion_sort.lt](../conformance/ported/insertion_sort.lt), [ported/swift_tuples.lt](../conformance/ported/swift_tuples.lt), [std/inout_map_default.lt](../conformance/std/inout_map_default.lt), [std/retain_with_raising_keep.lt](../conformance/std/retain_with_raising_keep.lt), [std/sort_through_inout.lt](../conformance/std/sort_through_inout.lt), [values/inout_map_entry.lt](../conformance/values/inout_map_entry.lt), [values/inout_on_raise.lt](../conformance/values/inout_on_raise.lt), [values/inout_raise_through_calls.lt](../conformance/values/inout_raise_through_calls.lt), [values/inout_self_on_raise.lt](../conformance/values/inout_self_on_raise.lt), [values/passed_inout_parameter.lt](../conformance/values/passed_inout_parameter.lt), [values/passed_on_raise_paths.lt](../conformance/values/passed_on_raise_paths.lt), [verification/order_caught.lt](../conformance/verification/order_caught.lt).

## Evaluation order

<a id="values.left-to-right"></a>
Evaluation is strictly left to right. This applies to:

- the arguments of a call, a method's receiver first;
- a called expression other than a name, which is evaluated before the arguments;
- the operands of a binary operator, except that `&&` and `||` evaluate their right operand only when the left one doesn't decide the result ([expressions.conditions](08-expressions.md#expressions.conditions));
- the elements of a tuple or a list;
- the fields of a record literal, in the order they are written, not the order they are declared;
- the splices of an interpolated string, each of which is shown and formatted before the next is evaluated.

Tests: [expressions/logical_short_circuit.lt](../conformance/expressions/logical_short_circuit.lt), [values/arguments_left_to_right.lt](../conformance/values/arguments_left_to_right.lt), [values/called_expression_before_arguments.lt](../conformance/values/called_expression_before_arguments.lt), [values/evaluation_order.lt](../conformance/values/evaluation_order.lt), [values/splice_shown_before_next.lt](../conformance/values/splice_shown_before_next.lt), [values/splices_left_to_right.lt](../conformance/values/splices_left_to_right.lt), [verification/order_shifted.lt](../conformance/verification/order_shifted.lt).

<a id="values.inout-argument-order"></a>
The index expressions of an `inout` argument's place, or of the place of a receiver taken `inout self`, are evaluated in that argument's turn. The place itself is read when the call starts, after every argument has been evaluated. The places of a call are read from left to right, and each read panics wherever reading the place would. So a change that a later argument makes to the place reaches the callee: `xs.push(xs.pop() else 0)` pushes onto the list that `pop` left. When the call returns or raises, each `inout` argument is written back, from left to right.

Tests: [modes/disjoint_inout.lt](../conformance/modes/disjoint_inout.lt), [values/inout_argument_order.lt](../conformance/values/inout_argument_order.lt), [values/inout_map_entry.lt](../conformance/values/inout_map_entry.lt), [values/inout_missing_key.lt](../conformance/values/inout_missing_key.lt), [values/inout_on_raise.lt](../conformance/values/inout_on_raise.lt), [values/inout_read_before_later_arguments.lt](../conformance/values/inout_read_before_later_arguments.lt), [values/inout_read_panics.lt](../conformance/values/inout_read_panics.lt), [values/receiver_order.lt](../conformance/values/receiver_order.lt), [values/receiver_read_panics.lt](../conformance/values/receiver_read_panics.lt), [verification/order_argument_cleared.lt](../conformance/verification/order_argument_cleared.lt), [verification/order_inserted.lt](../conformance/verification/order_inserted.lt).

<a id="values.index-reads"></a>
An index `c[k]` that reads evaluates `c`, and reads the value it indexes, before it evaluates `k`. So a change that `k` makes to `c` doesn't reach the read: `xs[{ xs.clear(); 0 }]` on a list of one gives its element. A store or a compound assignment through `c[k]`, and an `inout` argument whose place goes through it, reach the place later ([values.assignment-order](#values.assignment-order), [values.compound-assignment-order](#values.compound-assignment-order), [values.inout-argument-order](#values.inout-argument-order)).

Tests: [values/indexed_value_before_index.lt](../conformance/values/indexed_value_before_index.lt), [verification/order_read_pushed.lt](../conformance/verification/order_read_pushed.lt), [verification/order_rejected.lt](../conformance/verification/order_rejected.lt).

<a id="values.assignment-order"></a>
`place = e` evaluates the place's index expressions, then `e`, then stores.

Tests: [modes/self_referencing_assignment.lt](../conformance/modes/self_referencing_assignment.lt), [values/evaluation_order.lt](../conformance/values/evaluation_order.lt), [values/nested_place_order.lt](../conformance/values/nested_place_order.lt), [values/store_after_value.lt](../conformance/values/store_after_value.lt), [verification/order_field_cleared.lt](../conformance/verification/order_field_cleared.lt), [verification/order_rejected.lt](../conformance/verification/order_rejected.lt), [verification/order_store_cleared.lt](../conformance/verification/order_store_cleared.lt), [verification/order_store_index.lt](../conformance/verification/order_store_index.lt).

<a id="values.compound-assignment-order"></a>
`place op= e` evaluates the place's index expressions once, then `e`, then reads the place, applies `op` and writes the result back. So `m[k] += e` on a map without a default panics with `missing-key` only after `e` has been evaluated.

Tests: [modes/self_referencing_assignment.lt](../conformance/modes/self_referencing_assignment.lt), [values/compound_reads_after_value.lt](../conformance/values/compound_reads_after_value.lt), [values/evaluation_order.lt](../conformance/values/evaluation_order.lt), [values/map_compound_order.lt](../conformance/values/map_compound_order.lt), [values/nested_place_order.lt](../conformance/values/nested_place_order.lt), [verification/order_rejected.lt](../conformance/verification/order_rejected.lt).
