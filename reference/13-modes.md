# 13. Modes and exclusivity

This chapter says what a place is, which accesses to places a body may make at the same time, and what can be modified. It then gives the modes that the compiler infers for every binding and the tools show. Last come the advanced tier's views, iterators and projections, which build on both. [The value model](05-values.md) defines copies, `inout` and the order of evaluation, and [Expressions](08-expressions.md) defines assignment and calls.

## Places and accesses

<a id="modes.places"></a>
A **place** is a variable followed by zero or more fields, tuple fields and indexes: `.field`, `.0` or `[index]`. A call of a projection is a place too, rooted in the call ([projections.call-is-place](#projections.call-is-place)). So is `v[i]` for a binding `v` of a view of a list ([projections.places-through-views](#projections.places-through-views)). A field read through an `Option` is not a place, and neither is a field or an element of one ([types.option-field-not-place](07-types.md#types.option-field-not-place)). A place is required in each of these positions:

- the target of an assignment;
- an `inout` argument;
- the receiver of a method that takes `inout self`;
- the operand of a `yield`.

Where a place is required, anything else is E0401, *not a place* ([expressions.places](08-expressions.md#expressions.places)).

Tests: [expressions/fields_through_options_nested_place.lt](../conformance/expressions/fields_through_options_nested_place.lt), [expressions/fields_through_options_not_a_place.lt](../conformance/expressions/fields_through_options_not_a_place.lt), [expressions/not_a_place.lt](../conformance/expressions/not_a_place.lt), [modes/places.lt](../conformance/modes/places.lt), [modes/shadow_in_loop.lt](../conformance/modes/shadow_in_loop.lt), [values/passed_temporaries.lt](../conformance/values/passed_temporaries.lt), [values/var_parts.lt](../conformance/values/var_parts.lt).

<a id="modes.overlap"></a>
Two places **overlap** when, after every index is removed from both, one is a prefix of the other. So `xs[i]` overlaps every access to `xs`, whatever `i` is, and `a.b` overlaps `a` and `a.b.c`, but not `a.c`.

Tests: [modes/change_while_reading.lt](../conformance/modes/change_while_reading.lt), [modes/disjoint_inout.lt](../conformance/modes/disjoint_inout.lt), [modes/iterate_indexed_place.lt](../conformance/modes/iterate_indexed_place.lt), [modes/iterate_nested_field.lt](../conformance/modes/iterate_nested_field.lt), [modes/overlap_ignores_indexes.lt](../conformance/modes/overlap_ignores_indexes.lt), [modes/overlapping_inout.lt](../conformance/modes/overlapping_inout.lt), [values/passed_overlapping_places.lt](../conformance/values/passed_overlapping_places.lt), [values/passed_then_reassigned.lt](../conformance/values/passed_then_reassigned.lt).

<a id="modes.kinds-of-access"></a>
An access to a place is a **read** or a **modification**. The modifications are an assignment, a compound assignment, passing an `inout` argument, and the receiver of a method that takes `inout self`. Every other use of a place is a read.

Tests: [modes/change_while_reading.lt](../conformance/modes/change_while_reading.lt), [modes/consumed_inside_iteration.lt](../conformance/modes/consumed_inside_iteration.lt), [modes/inout_method_on_self.lt](../conformance/modes/inout_method_on_self.lt), [modes/modify_while_iterating.lt](../conformance/modes/modify_while_iterating.lt), [modes/reads_while_iterating.lt](../conformance/modes/reads_while_iterating.lt).

<a id="modes.durations"></a>
An access lasts for a span of the source text. A call first evaluates its arguments, its receiver included, from left to right ([values.left-to-right](05-values.md#values.left-to-right)), and only then starts. An `inout` argument, or a receiver taken by `inout self`, is a modification from the start of the call until it returns. The callee may read it until then as well, so the call reads each such argument after the modifications of them all that start it ([modes.shared-holders](#modes.shared-holders)). A `let` argument, or a receiver taken by `self`, is a read that ends once it has been evaluated, before the call starts. The callee receives the value read, as an independent copy, whether it consumes it or not ([values.passing-values](05-values.md#values.passing-values)). In `for p in e { body }`, when `e` is a place, `e` is read for the whole of `body`. Any other read ends when its evaluation ends, and an assignment lasts only for the store itself.

Tests: [modes/change_while_reading.lt](../conformance/modes/change_while_reading.lt), [modes/consumed_and_inout.lt](../conformance/modes/consumed_and_inout.lt), [modes/consumed_inside_iteration.lt](../conformance/modes/consumed_inside_iteration.lt), [modes/consumed_with_inout_receiver.lt](../conformance/modes/consumed_with_inout_receiver.lt), [modes/copy_scopes.lt](../conformance/modes/copy_scopes.lt), [modes/iterate_indexed_place.lt](../conformance/modes/iterate_indexed_place.lt), [modes/iterate_nested_field.lt](../conformance/modes/iterate_nested_field.lt), [modes/iterate_non_place.lt](../conformance/modes/iterate_non_place.lt), [modes/modify_while_iterating.lt](../conformance/modes/modify_while_iterating.lt), [modes/read_before_call.lt](../conformance/modes/read_before_call.lt), [modes/reads_while_iterating.lt](../conformance/modes/reads_while_iterating.lt), [modes/self_referencing_assignment.lt](../conformance/modes/self_referencing_assignment.lt), [modes/shared_storage_read_after.lt](../conformance/modes/shared_storage_read_after.lt), [promises/copies_read_where_no_name_is.lt](../conformance/promises/copies_read_where_no_name_is.lt), [values/argument_copies.lt](../conformance/values/argument_copies.lt), [values/inout_argument_order.lt](../conformance/values/inout_argument_order.lt), [values/inout_read_before_later_arguments.lt](../conformance/values/inout_read_before_later_arguments.lt), [values/inout_read_panics.lt](../conformance/values/inout_read_panics.lt), [values/receiver_order.lt](../conformance/values/receiver_order.lt), [values/receiver_read_panics.lt](../conformance/values/receiver_read_panics.lt).

## The law of exclusivity

<a id="modes.law"></a>
While an access to a place is in progress, no access to an overlapping place may begin if either of the two is a modification. Two modifications that begin together, at the start of the same call, may not overlap either. Reads may overlap freely. Views read and write their sources for durations of their own ([views.reads-that-last](#views.reads-that-last), [projections.what-view-writes](#projections.what-view-writes)). A projection's call holds its arguments for the access it serves ([projections.when-projection-runs](#projections.when-projection-runs)). The names of one `when` whose values have the same type count as one binding ([shared.names-that-may-be-one-place](14-tasks.md#shared.names-that-may-be-one-place)).

Tests: [expressions/closure_inout_captures.lt](../conformance/expressions/closure_inout_captures.lt), [modes/disjoint_inout.lt](../conformance/modes/disjoint_inout.lt), [modes/overlap_ignores_indexes.lt](../conformance/modes/overlap_ignores_indexes.lt), [modes/overlapping_inout.lt](../conformance/modes/overlapping_inout.lt), [ported/insertion_sort.lt](../conformance/ported/insertion_sort.lt), [values/inout_read_before_later_arguments.lt](../conformance/values/inout_read_before_later_arguments.lt).

<a id="modes.overlapping-inout"></a>
Two overlapping `inout` arguments of one call are E0402, *overlapping `inout` arguments*, at the later of the two places. So is an `inout` argument that overlaps an `inout self` receiver. So `swap(inout a, inout a)`, `f(inout a.b, inout a)`, and `a.f(inout a.b)` where `f` takes `inout self`, are each E0402. Other arguments are read before the call starts, so `xs.push(xs.len())`, `xs.push(xs[0])` and `f(inout a, a)` are accepted. In the last one, `f` receives the value `a` had before the call.

Tests: [expressions/closure_inout_captures.lt](../conformance/expressions/closure_inout_captures.lt), [modes/consumed_with_inout_receiver.lt](../conformance/modes/consumed_with_inout_receiver.lt), [modes/disjoint_inout.lt](../conformance/modes/disjoint_inout.lt), [modes/overlap_ignores_indexes.lt](../conformance/modes/overlap_ignores_indexes.lt), [modes/overlap_reported_at_later.lt](../conformance/modes/overlap_reported_at_later.lt), [modes/overlapping_inout.lt](../conformance/modes/overlapping_inout.lt), [modes/read_before_call.lt](../conformance/modes/read_before_call.lt).

<a id="modes.change-while-iterating"></a>
Inside the body of a `for` loop over a place, a modification of an overlapping place is E0404, *changing a list while reading it*, at the modification. That includes a modification through a call that takes the place `inout`, and through a method with `inout self` on a place that contains it. An example is `cart.remove(id)` inside `for item in cart.items`. A modification that conflicts with several reads, as inside two nested `for` loops over one list, gets one E0404. A loop over a value that isn't a place, such as `xs.enumerate(0)`, iterates that value, so its body may modify `xs`. The error offers two fixes: `retain` ([std.list-changes](17-std.md#std.list-changes)), or collecting the changes during the loop and applying them after it.

Tests: [checking/phases.lt](../conformance/checking/phases.lt), [expressions/closure_inout_captures.lt](../conformance/expressions/closure_inout_captures.lt), [modes/change_while_reading.lt](../conformance/modes/change_while_reading.lt), [modes/e0412_fixes.lt](../conformance/modes/e0412_fixes.lt), [modes/iterate_indexed_place.lt](../conformance/modes/iterate_indexed_place.lt), [modes/iterate_nested_field.lt](../conformance/modes/iterate_nested_field.lt), [modes/iterate_non_place.lt](../conformance/modes/iterate_non_place.lt), [modes/modify_while_iterating.lt](../conformance/modes/modify_while_iterating.lt), [modes/push_in_nested_loops.lt](../conformance/modes/push_in_nested_loops.lt), [modes/shadow_in_loop.lt](../conformance/modes/shadow_in_loop.lt).

<a id="modes.closures"></a>
A closure captures by copy and can't modify what it captures ([expressions.capture](08-expressions.md#expressions.capture)). So in core a closure never causes a violation of the law of exclusivity. A closure that captures a view reads the view's sources, as the view does ([views.fixed](#views.fixed)).

Tests: [expressions/closure_modifies_capture.lt](../conformance/expressions/closure_modifies_capture.lt), [modes/reads_while_iterating.lt](../conformance/modes/reads_while_iterating.lt), [modes/unmodifiable_takes_no_part.lt](../conformance/modes/unmodifiable_takes_no_part.lt).

<a id="modes.what-can-be-modified"></a>
Only `var` bindings and `inout` parameters can be modified. `let` bindings and `let` parameters can't, receivers taken by `self` among them. Neither can the bindings that a pattern makes outside a `var` ([patterns.var-bindings](09-patterns.md#patterns.var-bindings)). Modifying any of them is E0403, *modifying what can't be modified*, at the place modified. That error is reported alone: the modification takes no part in the law, so it never also gives E0402 or E0404. A parameter that the callee needs to modify is rebound with `var x = x`.

Tests: [checking/unmodifiable_with_missing_arm.lt](../conformance/checking/unmodifiable_with_missing_arm.lt), [checking/unmodifiable_with_type_error.lt](../conformance/checking/unmodifiable_with_type_error.lt), [expressions/closure_inout_captures.lt](../conformance/expressions/closure_inout_captures.lt), [expressions/closure_inout_parameters.lt](../conformance/expressions/closure_inout_parameters.lt), [expressions/closure_modifies_capture.lt](../conformance/expressions/closure_modifies_capture.lt), [modes/inout_method_on_self.lt](../conformance/modes/inout_method_on_self.lt), [modes/let_list_push.lt](../conformance/modes/let_list_push.lt), [modes/read_only_bindings.lt](../conformance/modes/read_only_bindings.lt), [modes/rebinding.lt](../conformance/modes/rebinding.lt), [modes/self_modes.lt](../conformance/modes/self_modes.lt), [modes/unmodifiable_takes_no_part.lt](../conformance/modes/unmodifiable_takes_no_part.lt), [modes/var_patterns.lt](../conformance/modes/var_patterns.lt), [patterns/bindings_immutable.lt](../conformance/patterns/bindings_immutable.lt), [ported/hylo_illegal_mutation.lt](../conformance/ported/hylo_illegal_mutation.lt), [values/let_immutable.lt](../conformance/values/let_immutable.lt).

## Modes

<a id="modes.bindings-and-axes"></a>
A **mode** is a fact of a **binding**: a `let` or `var` binding, a parameter, or a closure literal, which the rules treat as a binding of the closure value. Each binding has one point on each of five axes:

| Axis | Points | Default | The question it answers |
| --- | --- | --- | --- |
| locality | `local` < `escapes` | `local` | Does the value leave the function that binds it? |
| uniqueness | `unique` < `shared` | `unique` | At a write, may another path to the value exist? |
| once | `once` < `many` | `many` for a closure, none otherwise | May the closure run more than once? |
| portability | `portable` < `fixed` | `portable` | May the value go to another task? |
| contention | `calm` < `contended` | `calm` | May several tasks reach the value at once? |

The points of an axis are ordered as written. Inference finds the least point each rule allows, and never lifts a value above it. Nothing a program writes names a mode: `own`, `local`, `unique`, `once`, `portable` and `contended` are ordinary identifiers everywhere.

Checked by: the facts suite (`tests/facts/`), which `just facts` checks (`compiler/stilt-cli/tests/facts.rs`), and the toolchain's tests of `stilt show` (`compiler/stilt-cli/tests/show.rs`).

<a id="modes.fact-not-type"></a>
Modes are facts, as implicit effects are ([facts.interfaces](15-facts.md#facts.interfaces)). They are recorded per function in the module interface, apart from the signatures. Type checking never reads them, and editing a body changes the modes of that body alone. A function's type is its parameters' types and modes, `let` or `inout`, its result and its row ([declarations.function-types](10-declarations.md#declarations.function-types)). So none of a binding's five modes is part of it, and no two functions differ in type by one. The checks that a feature builds on modes run after type checking, with the law of exclusivity, as `without panic` does. A binding's modes are no part of a package's API ([versions.facts-in-api](21-versions.md#versions.facts-in-api)).

Checked by: the toolchain's tests of `stilt show --json`, whose record carries modes apart from the signature (`compiler/stilt-cli/tests/show.rs`), and the facts suite, which `just facts` checks.

## Locality

<a id="modes.escaping"></a>
Locality is a fact of bindings whose type is a copy-on-write type ([modes.copy-on-write-types](#modes.copy-on-write-types)). Every other binding is `local`. A binding **escapes** at the first place in source order where its value, or a part of it of a copy-on-write type, leaves the function. The value leaves the function where the body does one of these with it:

- returns it or raises it;
- stores it in a value;
- captures it in a closure literal that escapes;
- passes it to a parameter that its callee consumes.

A body stores a value in another where it puts the value in a record, tuple, list or map literal, or in a variant constructor's argument. It stores it too where it assigns it to an `inout` parameter, to a part of another binding, or through an index. An assignment to the whole of another local is a copy ([modes.copies](#modes.copies)), and a binding that does none of these is `local`. For a parameter, escaping is consumption, which [values.consumed-parameters](05-values.md#values.consumed-parameters) decides.

Checked by: the facts suite, whose `tests/facts/locality.lt` gives `ESCAPES x` at each line where a binding escapes, which `just facts` checks, and the toolchain's tests of `stilt show`.

<a id="modes.not-escaping"></a>
Passing a binding, or a part of it, as an `inout` argument doesn't make it escape ([values.inout-arguments](05-values.md#values.inout-arguments)). Capturing a binding in a closure literal makes the binding escape only when the closure escapes. So a binding captured by a closure that is only called in its function stays `local`.

Checked by: the facts suite, whose `tests/facts/locality.lt` prints nothing for such bindings, which `just facts` checks.

## Uniqueness

<a id="modes.copy-on-write-types"></a>
The **copy-on-write types** are `str`, `List<T>`, `Map<K, V>`, function types, recursive types ([facts.allocation](15-facts.md#facts.allocation)), and record, tuple, array and variant types with a field, element or payload of one. An array holds its elements inline, as a tuple does ([generics.array-effects](07-types.md#generics.array-effects)). Uniqueness, like locality, is a fact of bindings of these types: every other binding is `unique`.

Tests: [checking/copies_of_a_broken_field.lt](../conformance/checking/copies_of_a_broken_field.lt), [modes/array_copies.lt](../conformance/modes/array_copies.lt).

Checked by: the facts suite, whose `tests/facts/uniqueness.lt` gives no `SHARED` to a binding of a scalar type, which `just facts` checks.

<a id="modes.copies"></a>
A **copy** of a binding is made where its value, or a part of it of a copy-on-write type, is used in one of these ways:

- bound by a `let`, a `var` or a pattern;
- assigned to the whole of another local;
- captured by a closure literal;
- stored in a value ([modes.escaping](#modes.escaping));
- passed, other than as an `inout` argument, to a call that may store it ([modes.call-stores](#modes.call-stores));
- passed to a consumed parameter of a call after which the binding is used again, or to which it is passed twice.

A copy of a copy is a copy of the binding, held by whatever holds it. A binding passed to a consumed parameter where that makes no copy of it passes on the copies it holds, as a copy of it would. A copy lasts until the end of the scope of the binding that holds it. A copy stored in a value lasts until the end of the scope of the binding the value ends in. It lasts for the rest of the function when that binding escapes. A copy passed to a consumed parameter, or to a call that may store it, may end in the call's result or in any of its `inout` arguments, its receiver among them, as `xs.push(b)` stores `b` in `xs`. So it lasts as long as the longest of these:

- the call, when the result is dropped;
- the scope of the binding that holds the result;
- the scope of each binding that an `inout` argument is a part of;
- the rest of the function, when the result escapes or such a binding does.

So in `{ let b = a; xs.push(b) }` followed by `a.push(1)`, the push to `a` is shared while `xs` lasts ([modes.shared-writes](#modes.shared-writes)).

Tests: [modes/consumed_copies.lt](../conformance/modes/consumed_copies.lt), [modes/copies_in_closures_and_branches.lt](../conformance/modes/copies_in_closures_and_branches.lt), [modes/copies_of_held_parts.lt](../conformance/modes/copies_of_held_parts.lt), [modes/copies_stored_by_calls.lt](../conformance/modes/copies_stored_by_calls.lt), [modes/copies_stored_in_inout_arguments.lt](../conformance/modes/copies_stored_in_inout_arguments.lt), [modes/copy_scopes.lt](../conformance/modes/copy_scopes.lt), [modes/copy_ways.lt](../conformance/modes/copy_ways.lt), [modes/element_copies.lt](../conformance/modes/element_copies.lt), [modes/shared_writes_along_paths_accepted.lt](../conformance/modes/shared_writes_along_paths_accepted.lt).

Checked by: the facts suite, whose `tests/facts/uniqueness.lt` makes each kind of copy before a write, which `just facts` checks.

<a id="modes.call-stores"></a>
A call **may store** an argument passed other than as an `inout` argument when, by the types of the call, a part of the argument's value may become a part of its result or of one of its `inout` arguments. The parts of a value of a type are the type itself, when it is a copy-on-write type ([modes.copy-on-write-types](#modes.copy-on-write-types)), and the parts of what it holds: a list's elements, a map's keys and values, an array's elements, a tuple's elements, a record's fields, a variant's payloads, and for a function type, the values its calls give back and those they write through its `inout` parameters. A recursive type holds its fields and payloads, and those hold the type again, at whatever arguments; only the copy-on-write parts count. A part may become a part of another value when the argument's part and a part of the other value have the same type, when either is a type parameter, `Self`, a constructor applied, a spread or a handler's type, which may stand for any type, or when the other value's part has a function type, whose closures may capture any value. So `xs.push(b)` may store `b` in `xs`, `xs.get(0)` may store `xs` in its result when `xs` is a `List<List<i64>>` but not when it is a `List<i64>`, and `xs.len()` stores nothing. This rule reads only the types of the call, so it holds of a native function, whose body the program doesn't see, as of any other.

Tests: [modes/copies_stored_in_inout_arguments.lt](../conformance/modes/copies_stored_in_inout_arguments.lt), [modes/copies_stored_by_calls.lt](../conformance/modes/copies_stored_by_calls.lt).

<a id="modes.shared-writes"></a>
A `var` binding or an `inout` parameter is **shared** at a modification of it, or of a part of it, when a copy of the modified part might still last there, or when the modified part is inside a copy that the binding holds of another binding's part while that binding might still read it ([modes.shared-holders](#modes.shared-holders)). A copy might still last at the modification when a path from where the copy is made reaches the modification while the copy lasts ([modes.copies](#modes.copies)), without leaving, once inside it, the scope whose end ends the copy, and with no assignment of the whole binding, and no binding of it anew, on the way. The paths are those that execution may take through the body ([modes.shared-paths](#modes.shared-paths)). A loop binds the bindings of its body anew on each turn, so copies of such a binding made on an earlier turn don't count for its modifications. So `let b = a` followed by `a.push(1)` is shared while `b` lasts. An assignment of the whole binding is never shared: it replaces the binding's value and copies nothing. The fact is at the modification, and a binding with no shared modification is `unique`.

Tests: [modes/array_copies.lt](../conformance/modes/array_copies.lt), [modes/consumed_copies.lt](../conformance/modes/consumed_copies.lt), [modes/copies_in_closures_and_branches.lt](../conformance/modes/copies_in_closures_and_branches.lt), [modes/copies_of_held_parts.lt](../conformance/modes/copies_of_held_parts.lt), [modes/copies_stored_by_calls.lt](../conformance/modes/copies_stored_by_calls.lt), [modes/copies_stored_in_inout_arguments.lt](../conformance/modes/copies_stored_in_inout_arguments.lt), [modes/copy_scopes.lt](../conformance/modes/copy_scopes.lt), [modes/copy_ways.lt](../conformance/modes/copy_ways.lt), [modes/element_copies.lt](../conformance/modes/element_copies.lt), [modes/handles.lt](../conformance/modes/handles.lt), [modes/shared_writes_along_paths.lt](../conformance/modes/shared_writes_along_paths.lt), [modes/shared_writes_along_paths_accepted.lt](../conformance/modes/shared_writes_along_paths_accepted.lt), [modes/shared_writes_in_when.lt](../conformance/modes/shared_writes_in_when.lt), [promises/copies.lt](../conformance/promises/copies.lt), [promises/copies_read_after_the_body.lt](../conformance/promises/copies_read_after_the_body.lt), [promises/copies_read_by_another_holder.lt](../conformance/promises/copies_read_by_another_holder.lt), [promises/copies_read_where_no_name_is.lt](../conformance/promises/copies_read_where_no_name_is.lt), [promises/in_place_elements_rejected.lt](../conformance/promises/in_place_elements_rejected.lt), [promises/stored_copies.lt](../conformance/promises/stored_copies.lt).

Checked by: the facts suite, whose `tests/facts/uniqueness.lt` gives `SHARED x` at each shared write, which `just facts` checks.

<a id="modes.shared-self-parts"></a>
An assignment whose value holds a part of the binding's own value, read from the binding or from another binding that holds a copy of it, as `x = x.next` does, and `x = y` after `let y = x`, is no assignment of the whole for [modes.shared-writes](#modes.shared-writes). On a path through it, a copy made before it, or held by a binding before it, counts as a copy of every part of the binding, for the binding's own modifications and for those of the bindings that hold such a copy. So `let z = x` followed by `x = x.kids[0]` and `x.items.push(1)` is shared while `z` lasts, and `var z = u` followed by `u = u.kids[0]`, `let w = u.items` and `z.kids[0].items.push(1)` is shared while `w` lasts.

Tests: [modes/shared_writes_along_paths.lt](../conformance/modes/shared_writes_along_paths.lt), [promises/copies_read_after_the_body.lt](../conformance/promises/copies_read_after_the_body.lt).

<a id="modes.shared-holders"></a>
A binding that holds a copy of another binding's part is shared at a modification of a part inside the copy while the other binding, or another binding that holds a copy of the part, might still read the part. The binding holds the copy at the modification when a path from where it was given the copy reaches the modification with no assignment to it that replaces the place that holds the copy, and no binding of it anew, on the way: its value is the copy, or holds it as a field of a record or tuple literal, an element of a list literal or a part assigned to. A binding that copies of copies give parts of one another around a loop may hold a copy of any part below the part they copy.

The other binding might still read the part when a path from where it was given the part goes through the modification on to a read of it ([modes.kinds-of-access](#modes.kinds-of-access)), with no assignment of its whole, and no binding of it anew, on the way, or when it is read when the body that holds the modification ends: an `inout` parameter of that body, whose value goes back to the caller when the call returns, or a variable that the body, a closure literal's, captures, which the closure's next call reads. The other binding may be a parameter, a `let` or a `var`, or a name that a pattern or a `when` binds, a `for`'s, a `match` arm's or a `catch`'s among them, and a `for` loop over a place reads the place on each turn ([modes.durations](#modes.durations)). The end of a `when` reads each of its names, whose values it gives back to their handles ([modes.handles](#modes.handles)). A call reads each of its `inout` arguments, its receiver among them, after the modifications of them all that start it, until it returns ([modes.durations](#modes.durations)); that read counts for those modifications alone, since for an earlier one the call's modification of the argument is itself shared while the copy lasts. The binding whose part was copied counts only while it may still have the value that the modified copy was made from, since a path through an assignment of its whole doesn't count. The other bindings that hold a copy of the part count whichever value of that binding they copied, before or after an assignment of its whole. So `var b = a` followed by `b.push(1)` is shared when `a` is read after the push, or is an `inout` parameter or a captured variable, and so is `var p = Pair { left: a, right: [] }` followed by `p.left.push(1)`, but not `p.right.push(1)`. In `when a { var z = a; z[0] = 9 }`, the write to `z` is shared, and so are both arguments of `both(inout b, inout c)` after `var b = t` and `var c = t`, whatever `both` does with them. After `var z = o`, `let w = o` and `o = t`, `z[0] = 9` is shared when `w` is read after it, and not when only `o` is.

Tests: [modes/copies_of_held_parts.lt](../conformance/modes/copies_of_held_parts.lt), [modes/handles.lt](../conformance/modes/handles.lt), [modes/shared_storage_read_after.lt](../conformance/modes/shared_storage_read_after.lt), [modes/shared_writes_along_paths.lt](../conformance/modes/shared_writes_along_paths.lt), [modes/shared_writes_in_when.lt](../conformance/modes/shared_writes_in_when.lt), [promises/copies.lt](../conformance/promises/copies.lt), [promises/copies_read_after_the_body.lt](../conformance/promises/copies_read_after_the_body.lt), [promises/copies_read_by_another_holder.lt](../conformance/promises/copies_read_by_another_holder.lt), [promises/copies_read_where_no_name_is.lt](../conformance/promises/copies_read_where_no_name_is.lt), [promises/stored_copies.lt](../conformance/promises/stored_copies.lt).

<a id="modes.shared-when-names"></a>
A `when`'s name is a `var` binding for [modes.shared-writes](#modes.shared-writes), since it is written as one ([shared.when](14-tasks.md#shared.when)). The names of one `when` whose values have the same type may be one place ([shared.names-that-may-be-one-place](14-tasks.md#shared.names-that-may-be-one-place)), so for this rule a modification of a part of one is a modification of that part of each, and a read of one is a read of each. An assignment to one replaces nothing of the others. So in `when a, b`, of two `Shared<List<i64>>` values, `let c = a` followed by `b.push(1)` is shared while `c` lasts, and `var y = a` followed by `y.push(1)` is shared when `b` is read after the push.

Tests: [modes/shared_writes_in_when.lt](../conformance/modes/shared_writes_in_when.lt).

<a id="modes.handles"></a>
The end of a `when` gives each name's value back to its handle, where a later `when`, in any function, may write it ([shared.when](14-tasks.md#shared.when)). So for [modes.shared-writes](#modes.shared-writes), the end of a `when` modifies each of its names, and for [modes.shared-holders](#modes.shared-holders) it reads each of them first, after every point of the block. What a name holds lasts on, held by the handle, and the `when`'s value is held by what holds the `when`'s. A copy of a part of a name's value that lasts past the `when`, as one that the block gives as its value does, makes the end shared. So does a copy that a name holds of another binding's part that the other binding might still read after the `when` ([modes.shared-holders](#modes.shared-holders)). A call of `Shared.new` gives the value it takes to a handle in the same way: it is shared when the binding whose value it takes might still read it after the call, as a parameter's caller may, and as a read on a path from the call does. The fact is at the `when` or at the call, as a caller's is at an `inout` argument that its callee writes. So in `fn grab(a: Shared<List<i64>>) -> List<i64> { when a { a } }`, the `when` copies, and `when a { a.push(1) }`, in another function, copies nothing, while in `when a { var z = a; z[0] = 9 }` the write to `z` copies, since the end of the `when` reads `a` after it.

Tests: [modes/handles.lt](../conformance/modes/handles.lt), [modes/shared_storage_read_after.lt](../conformance/modes/shared_storage_read_after.lt), [promises/copies_read_where_no_name_is.lt](../conformance/promises/copies_read_where_no_name_is.lt).

<a id="modes.shared-paths"></a>
The paths that execution may take go through each expression in the order of evaluation ([values.left-to-right](05-values.md#values.left-to-right)). An `if`, an `if let`, a `match`, an `else`, `&&` and `||` take one of their branches, or skip the one that may be skipped, and their paths meet after them. A loop may run no turn or many: its head is reached from before it, from the end of each turn and from each `continue`, and what follows it from each `break` and, unless it is a `loop`, from its head, after a `while`'s condition. A `return` leaves the body, and so does a raise outside every `try` of the body. Any point of a `try`'s operand may go to the arms of its `catch`, as a raise or a call that raises there does, and any point of a `with`'s block may go to what follows the `with`, since a handler may not resume. A spread's body may run any number of times. A closure literal's body is on a path from the literal back to it, as if a call ran it there. So in `loop { if done { w = x; break }; w = [] }` followed by `w.push(1)`, the push is shared while `x` is read after it, since the `break` skips `w = []`.

Tests: [modes/copies_in_closures_and_branches.lt](../conformance/modes/copies_in_closures_and_branches.lt), [modes/shared_writes_along_paths.lt](../conformance/modes/shared_writes_along_paths.lt), [modes/shared_writes_along_paths_accepted.lt](../conformance/modes/shared_writes_along_paths_accepted.lt).

<a id="modes.shared-conservative"></a>
[modes.shared-writes](#modes.shared-writes) is conservative, as durations are ([modes.durations](#modes.durations)). A copy held by a binding counts until the binding's scope ends, whether or not the binding is used again, and every path counts, whatever the values that decide which one runs. A write in place through an element of a list that holds its own storage is never shared ([facts.writes-in-place](15-facts.md#facts.writes-in-place)). The implicit effect `copy` reads the shared writes ([facts.copy](15-facts.md#facts.copy)).

Tests: [modes/copy_scopes.lt](../conformance/modes/copy_scopes.lt), [promises/in_place_elements_rejected.lt](../conformance/promises/in_place_elements_rejected.lt).

## Once

<a id="modes.once-closures"></a>
A closure literal is `once` in each of these cases:

- it is called where it is written;
- it is passed, where it is written, as an argument to a `once` parameter ([modes.once-parameters](#modes.once-parameters)), even inside a loop;
- it is bound by a `let` whose binding is used exactly once in its scope, in a call or a pass to a `once` parameter. That use is outside every loop and every closure literal of the scope.

Every other closure literal is `many`. The fact is at the closure literal.

Checked by: the facts suite, whose `tests/facts/once.lt` gives `ONCE f` and `ONCE` at such closures, which `just facts` checks, and the toolchain's tests of `stilt show`.

<a id="modes.once-parameters"></a>
A parameter of function type is `once` when both of these hold:

- the body uses it exactly once, outside every loop and every closure literal;
- that use is a call, or a pass to a `once` parameter of a callee.

Recursive groups of functions are solved as a fixed point over the call graph, starting from `once`, as implicit effects are ([facts.inference](15-facts.md#facts.inference)). The fact is at the one use. A `once` closure may give its captures up at its call, as a consumed parameter may reuse its argument ([values.consumed-parameters](05-values.md#values.consumed-parameters)). Nothing a program can observe depends on it.

Checked by: the facts suite, whose `tests/facts/once.lt` holds parameters called once, in loops and in recursive groups, which `just facts` checks; the toolchain's tests of `stilt show`; and the compiler's tests of consumption (`compiler/stilt-rc/src/consume/tests.rs`).

## Portability and contention

<a id="modes.fixed-values"></a>
A binding is `fixed` when its type holds a fixed type, or when it is a closure literal that captures a fixed binding. The fixed types are `View<T>` and `Iter<T>` ([views.fixed](#views.fixed)). So no core type is fixed, and every binding of a core module is `portable`.

Tests: [par/demanded_arguments.lt](../conformance/par/demanded_arguments.lt), [par/held_through_declarations.lt](../conformance/par/held_through_declarations.lt).

Checked by: the facts suite, whose core programs print no `FIXED`, and whose `tests/facts/views.lt` gives every view binding its source, which stands for `fixed`; `just facts` checks both.

<a id="modes.contended-values"></a>
A binding is `contended` when its type holds `Shared<T>` ([shared.std-sync](14-tasks.md#shared.std-sync)), or when it is a closure literal that captures a contended binding. No core type is contended, so every binding of a core module is `calm`. `Shared<T>` is `portable`.

Tests: [par/demanded_arguments.lt](../conformance/par/demanded_arguments.lt), [par/function_types_hold_nothing.lt](../conformance/par/function_types_hold_nothing.lt), [par/held_through_declarations.lt](../conformance/par/held_through_declarations.lt), [par/held_through_declarations_accepted.lt](../conformance/par/held_through_declarations_accepted.lt).

Checked by: the facts suite, whose core programs print no `CONTENDED`, which `just facts` checks; the conformance tests of [shared.tasks-and-modes](14-tasks.md#shared.tasks-and-modes) and [par.what-runs-in-parallel](14-tasks.md#par.what-runs-in-parallel) check the demands that read it.

<a id="modes.mode-crossing"></a>
A type without mutable heap state of its own is neither fixed nor contended, whatever its contents. Every core type is such a type, since a value appears to change only through a `var` or an `inout` ([values.value-semantics](05-values.md#values.value-semantics)). So the thread axes read a type's declaration once, and never its values' history. The one way to be contended is to hold a `Shared<T>`, and the one way to be fixed is to hold a fixed type.

Tests: [par/function_types_hold_nothing.lt](../conformance/par/function_types_hold_nothing.lt), [par/held_through_declarations.lt](../conformance/par/held_through_declarations.lt), [par/held_through_declarations_accepted.lt](../conformance/par/held_through_declarations_accepted.lt).

Checked by: the facts suite, which `just facts` checks; the conformance tests of [shared.tasks-and-modes](14-tasks.md#shared.tasks-and-modes) and [par.what-runs-in-parallel](14-tasks.md#par.what-runs-in-parallel) check the types that hold a fixed or contended one.

## Demands

<a id="modes.demands"></a>
A feature that needs a value's mode states a **demand**: the least point on an axis that a use accepts. A demand is checked where the use is written, against the mode that the rules of this chapter give, after type checking. It never changes a type. These features state demands:

- A closure that a function of `std.par` runs must be `calm` and `portable` (E0431, [par.what-runs-in-parallel](14-tasks.md#par.what-runs-in-parallel)).
- A value placed in a `Shared<T>`, and a task's function, must be `portable` (E0432, [shared.std-sync](14-tasks.md#shared.std-sync), [shared.tasks-and-modes](14-tasks.md#shared.tasks-and-modes)).
- A view escapes nowhere but into the result of a function ([views.escaping](#views.escaping)).

Every binding of a core module is `calm` and `portable`, and no core module holds a view, so no core program fails a check of modes.

Checked by: the conformance tests of each demand's own paragraph.

<a id="modes.diagnostic-shape"></a>
A diagnostic that a demand raises has one message line and one note. The message line names the binding and the axis in plain words, as in ``this closure can't run in parallel: it reaches `log`, which is contended``. The note is at the line where the binding gained the mode ([modes.escaping](#modes.escaping), [modes.shared-writes](#modes.shared-writes), [modes.once-closures](#modes.once-closures), [modes.fixed-values](#modes.fixed-values), [modes.contended-values](#modes.contended-values)). The message fits in 40 tokens, and lists its alternatives where it can.

Checked by: the snapshots of the codes that the demands give, in `tests/diagnostics/`, which `just diagnostics` checks.

## Showing modes

<a id="modes.show"></a>
`stilt show` and the language server print a binding's modes as they print consumption ([values.consumed-parameters](05-values.md#values.consumed-parameters)) and implicit effects ([facts.visibility](15-facts.md#facts.visibility)). They print them in two places:

- for parameters, in the function's bracket after its signature;
- at the line that causes the fact, in the comment that holds the line's other facts.

Only a mode other than the default is printed, with the words `escapes`, `shared`, `once`, `fixed` and `contended`. A parameter's locality is printed as its consumption, `consumes x`, and nothing else, and a `once` parameter prints `once f` in the bracket. A closure literal's modes are printed with the name of the `let` or `var` that binds it, as `once f`, and an unbound closure literal prints `once` alone. A closure literal's own locality is never printed. A module's skeleton leaves modes out, as it leaves every fact out.

Checked by: the toolchain's tests of `stilt show` and of the language server's hover (`compiler/stilt-cli/tests/show.rs`, `compiler/stilt-cli/tests/lsp.rs`), and the facts suite, which `just facts` checks.

<a id="modes.facts-suite"></a>
The facts suite (`tests/facts/`) has one annotation per printed word: `ESCAPES x`, `SHARED x`, `ONCE f`, `FIXED x` and `CONTENDED x`, and `ONCE` alone for an unbound closure literal, each at the line that [modes.show](#modes.show) gives. The expected facts are derived from the rules of this chapter by reasoning, never from an implementation.

Checked by: `just facts` (`compiler/stilt-cli/tests/facts.rs`).

## Views

<a id="views.std-view"></a>
The module `std.view` declares two **native types**, `pub type View<T> = ?` and `pub type Iter<T> = ?` (the `type_decl` production, [syntax.declarations](03-syntax.md#syntax.declarations)). A native type has no written representation, as a native function has no written body. Each implementation gives it one, and its functions are native. Only `std` declares native types. `View` and `Iter` join no prelude, and no prelude type gains a method. So a module that names either type is in the advanced tier ([program.module-tier](04-programs.md#program.module-tier)).

Checked by: the facts suite, whose `tests/facts/views.lt` carries `//~ tier: advanced`, which `just facts` checks, and the toolchain's tests of `stilt show`; the library's own sources declare the two types.

<a id="views.viewable-types"></a>
The **viewable types** are `str` and `List<U>`. A `View<T>` requires `T` viewable, and any other `T` is E0420, *not a viewable type*, where the type is written or inferred.

Tests: [checking/view_of_a_broken_type.lt](../conformance/checking/view_of_a_broken_type.lt), [views/not_viewable.lt](../conformance/views/not_viewable.lt), [views/view_types_in_signatures.lt](../conformance/views/view_types_in_signatures.lt).

<a id="views.what-view-is"></a>
A `View<T>` is a window into a part of a value of type `T`, its **source**, between a start and an end offset. The offsets are counted as `slice` counts them ([std.str](17-std.md#std.str), [std.lists](17-std.md#std.lists)): bytes of a `str`, elements of a `List<U>`. Reading through a view reads the source's part, and a view holds no copy. An `Iter<T>` is a lazy sequence of values of type `T`. Its elements come from its sources, through its adapters' closures, only when a consumer asks for them ([views.laziness](#views.laziness)).

Tests: [views/view_basics.lt](../conformance/views/view_basics.lt).

<a id="views.view-types"></a>
The **view types** are `View<T>`, `Iter<T>`, a closure type whose literal captures a value of a view type ([views.fixed](#views.fixed)), and `Option<V>` for a view type `V`. A view type may be the type of a local binding, a parameter, a function's result, a closure's capture, and a type argument of a generic function's call. Anywhere else, it is E0421, *a view can't be stored*, at the type. Such places include these:

- a field of a record;
- a variant's payload other than `Option`'s;
- an element of a `List` or a `Map`;
- a component of a tuple;
- a type argument of a declared type.

A generic function instantiated with a view type keeps this rule: `[v]` for a view `v` is E0421, through `List<T>`.

Tests: [views/stored.lt](../conformance/views/stored.lt), [views/stored_accepted.lt](../conformance/views/stored_accepted.lt), [views/temporaries.lt](../conformance/views/temporaries.lt), [views/view_types_in_signatures.lt](../conformance/views/view_types_in_signatures.lt).

<a id="views.making-view"></a>
`View.of<T>(source: T, start: i64, end: i64) -> View<T>` views the part of `source` from `start` up to `end`. It panics as `slice` does: with `bounds` unless `0 ≤ start ≤ end ≤ len`, and with `utf8-boundary` when an offset splits a character of a `str`. `View.all<T>(source: T) -> View<T>` views the whole. Both are in `impl<T> View<T>`, and a call whose `T` isn't viewable is E0420, at the argument. `v.view(start, end)` views a part of a view, with offsets counted from the view's start. The source of the view depends on the argument:

- when the argument is a place ([modes.places](#modes.places)), the source is the place;
- when the argument is a view, the sources are the sources of the argument;
- when the argument is any other expression, such as a call or a literal, the source is a temporary that lasts as long as the view.

Tests: [views/view_basics.lt](../conformance/views/view_basics.lt), [views/view_bounds.lt](../conformance/views/view_bounds.lt), [views/view_panics.lt](../conformance/views/view_panics.lt).

<a id="views.across-calls"></a>
For views, a `let` parameter of a viewable type has the caller's argument as its source, not the callee's copy. The two can't be told apart, since the argument can't change while the view lives ([views.reads-that-last](#views.reads-that-last)). A view parameter has the sources of its argument. The result of a call whose result type is a view type has as its sources the sources of every argument whose type is viewable or a view type. It writes those of them passed `inout` ([projections.what-view-writes](#projections.what-view-writes)). Inside the callee, a view in the result may have as sources only its `let` parameters of viewable type, its view parameters, and the `inout` parameters it writes ([projections.results-that-write](#projections.results-that-write)).

Tests: [views/escaping.lt](../conformance/views/escaping.lt), [views/result_views_both.lt](../conformance/views/result_views_both.lt), [views/result_views_parameter.lt](../conformance/views/result_views_parameter.lt), [views/stored_accepted.lt](../conformance/views/stored_accepted.lt), [views/temporaries.lt](../conformance/views/temporaries.lt).

<a id="views.escaping"></a>
A view never leaves the scope that binds one of its sources. So none of these reaches outside:

- a block whose value views a binding the block makes;
- the arm of a `match` or an `if let` whose value views a binding of its pattern;
- a `when` whose value views a name it holds, which stands for the place of a value the `when` releases when its block ends ([shared.when](14-tasks.md#shared.when));
- the value of a `for` body.

A view escapes a function ([modes.escaping](#modes.escaping)) only into its result, and only when every one of its sources is a parameter that [views.across-calls](#views.across-calls) allows. Any other escape is E0422, *a view outlives its source*, at the expression that escapes, naming the source. Among such escapes are these:

- a block's value that views the block's own binding;
- an assignment of a view to a variable bound outside the scope of one of its sources;
- returning a view of a local;
- capturing a view in a closure that escapes.

A view of an `inout` parameter in a result is the error of [projections.results-that-write](#projections.results-that-write) unless the result writes it.

Tests: [shared/views_in_when.lt](../conformance/shared/views_in_when.lt), [views/escaping.lt](../conformance/views/escaping.lt), [views/escaping_accepted.lt](../conformance/views/escaping_accepted.lt), [views/result_views_parameter.lt](../conformance/views/result_views_parameter.lt), [views/temporaries.lt](../conformance/views/temporaries.lt).

<a id="views.reads-that-last"></a>
A binding of a view type is a read of each of its sources that lasts for the binding's scope. It is like the read of `e` that `for p in e` makes for its body ([modes.durations](#modes.durations)). A view that no binding holds is a read of its sources until the end of the statement that holds the expression. A view passed to a parameter is a read of its sources for the call. The read of a source begins where the operand that gives the source is evaluated, before the operands after it ([values.left-to-right](05-values.md#values.left-to-right)): in `View.of(xs, a, b)`, where `xs` is evaluated, before `a` and `b`, and in a call that returns a view, where each argument that gives the result a source is evaluated. A source passed `inout` is read when the call starts ([values.inout-argument-order](05-values.md#values.inout-argument-order)), and its read begins there. The argument's read of [views.across-calls](#views.across-calls) lasts as long as the result's.

Tests: [views/durations.lt](../conformance/views/durations.lt), [views/durations_accepted.lt](../conformance/views/durations_accepted.lt), [views/read_starts_at_source.lt](../conformance/views/read_starts_at_source.lt), [views/read_starts_at_source_accepted.lt](../conformance/views/read_starts_at_source_accepted.lt), [views/temporaries.lt](../conformance/views/temporaries.lt).

<a id="views.change-while-viewed"></a>
While a view of a source lives, a modification of a place that overlaps the source is E0423, *changing a value while a view reads it*, at the modification. This is the law of exclusivity, applied to the view's read. It includes a later operand of the expression that makes the view, or of a call that a view is passed to, which changes a source that an earlier operand gives ([views.reads-that-last](#views.reads-that-last)). So with `fn bump(inout xs: List<i64>) -> i64`, the argument `inout xs` is E0423 in `View.of(xs, bump(inout xs), 2)`, in `View.of(xs, 0, bump(inout xs))` and in `f(View.all(xs), bump(inout xs))`. The error names the view and the line where its read ends. It is counted as E0404 is ([modes.change-while-iterating](#modes.change-while-iterating)). The error offers two fixes: make the change before the view, or end the view's binding's scope first.

Tests: [views/durations.lt](../conformance/views/durations.lt), [views/durations_accepted.lt](../conformance/views/durations_accepted.lt), [views/read_starts_at_source.lt](../conformance/views/read_starts_at_source.lt), [views/read_starts_at_source_accepted.lt](../conformance/views/read_starts_at_source_accepted.lt), [views/result_views_both.lt](../conformance/views/result_views_both.lt).

<a id="views.fixed"></a>
`View<T>` and `Iter<T>` are fixed types ([modes.fixed-values](#modes.fixed-values)), so every binding of a view type is `fixed`. A closure literal that captures one is fixed and has the captured view's sources. A view's locality follows [modes.escaping](#modes.escaping) and [views.escaping](#views.escaping).

Tests: [views/stored_accepted.lt](../conformance/views/stored_accepted.lt).

Checked by: the facts suite, whose `tests/facts/views.lt` gives `VIEWS x`, which stands for `fixed`, and which `just facts` checks, and the toolchain's tests of `stilt show`.

<a id="views.functions-of-views"></a>
What holds of every view is in `impl<T> View<T>`, and what holds of one viewed type is a function of `std.view`. All are native:

- in `impl<T> View<T>`: `len(self) -> i64` and `is_empty(self) -> bool`, the viewed part's; `view(self, start: i64, end: i64) -> View<T>` ([views.making-view](#views.making-view)); and `copy(self) -> T`, the viewed part as an owned value;
- `view.get<U>(v: View<List<U>>, i: i64) -> Option<U>`, and indexing, `v[i]` on a `View<List<U>>`, which panics with `bounds` as `xs[i]` does;
- `view.chars(v: View<str>) -> Iter<str>` and `view.bytes(v: View<str>) -> Iter<u8>`, the sequences that `chars` and `bytes` of `str` build eagerly.

`View<T>` has `Show`, `Eq`, `Ord` and `Hash` wherever `T` has them, each as the viewed part's. Two views are equal when their parts are, and a view shows as its part shows. A view and a value of `T` have different types, so `copy` compares them: `View.of("to be", 0, 2).copy() == "to"`. Of these functions, and `View.of` and `View.all`, `copy`, `view.chars` and `view.bytes` allocate, and the others hold the view inline and allocate nothing ([facts.native-allocation](15-facts.md#facts.native-allocation)). `View.of` and `view` panic with `bounds`, which their implicit effects carry.

Tests: [ported/swift_arrays.lt](../conformance/ported/swift_arrays.lt), [views/view_basics.lt](../conformance/views/view_basics.lt), [views/view_index_bounds.lt](../conformance/views/view_index_bounds.lt).

<a id="views.for-over-view"></a>
A `for` loop iterates a `View<List<U>>` and an `Iter<U>`, each yielding `U` ([expressions.for-iterables](08-expressions.md#expressions.for-iterables)). A `for` over an `Iter` allocates the state it pulls elements through, and one over a view allocates nothing ([facts.allocation](15-facts.md#facts.allocation)). Inside the body, the loop's view is a read of its sources ([views.reads-that-last](#views.reads-that-last)), so a modification of a source is E0423.

Tests: [implicit/allocating_natives.lt](../conformance/implicit/allocating_natives.lt), [implicit/allocation_free_natives.lt](../conformance/implicit/allocation_free_natives.lt), [views/for_over_views.lt](../conformance/views/for_over_views.lt).

## Iterators

<a id="views.making-iterator"></a>
`Iter.of(xs: List<T>) -> Iter<T>` and `Iter.of_view(v: View<List<T>>) -> Iter<T>`, in `impl<T> Iter<T>`, make an iterator with the sources of [views.making-view](#views.making-view). `view.of_map<K: Eq + Hash, V>(m: Map<K, V>) -> Iter<(K, V)>` iterates a map in insertion order, with the map as its source. `view.range(start: i64, end: i64) -> Iter<i64>` gives the integers from `start` up to but excluding `end`, with no source. These two are functions of `std.view`. A function of `impl<T> Iter<T>` that names no `T` would leave `T` undecided at a call ([types.undecided-types](07-types.md#types.undecided-types)). A range `a..b` is not a value ([expressions.ranges](08-expressions.md#expressions.ranges)).

Tests: [views/iterators.lt](../conformance/views/iterators.lt).

<a id="views.adapters"></a>
The **adapters**, all native, in `impl<T> Iter<T>`, each return an iterator whose sources are those of `self` and of every iterator argument:

- `map<U>(self, f: fn(T) -> U) -> Iter<U>`;
- `filter(self, keep: fn(T) -> bool) -> Iter<T>`;
- `take(self, n: i64) -> Iter<T>`, `skip(self, n: i64) -> Iter<T>`, `take_while(self, p: fn(T) -> bool) -> Iter<T>` and `skip_while(self, p: fn(T) -> bool) -> Iter<T>`;
- `enumerate(self, start: i64) -> Iter<(i64, T)>`;
- `zip<U>(self, other: Iter<U>) -> Iter<(T, U)>`, which ends when either ends;
- `chain(self, other: Iter<T>) -> Iter<T>`.

Each allocates the iterator it gives, which holds its sources and its closures, as every function of an iterator does ([facts.native-allocation](15-facts.md#facts.native-allocation)). An adapter's closure runs when a consumer asks for an element, so the parameter that takes it is `escaping`, with an empty row. The closure may panic and allocate. A closure literal that performs `io` or raises is E0502 there ([effects.inference](12-effects.md#effects.inference)), and a function value with a larger row is E0311. The iterator keeps the closure as a copy. The closure captures no view: one that does escapes with the view, which is E0422 at the closure ([views.escaping](#views.escaping)).

Tests: [implicit/allocating_natives.lt](../conformance/implicit/allocating_natives.lt), [procedural/numbers](../conformance/procedural/numbers/), [views/adapter_closure_captures_view.lt](../conformance/views/adapter_closure_captures_view.lt), [views/adapter_closure_rows.lt](../conformance/views/adapter_closure_rows.lt), [views/iterators.lt](../conformance/views/iterators.lt).

<a id="views.laziness"></a>
Nothing runs when an iterator is made or adapted. A consumer asks for elements one at a time. Each element passes through the adapters from the source outward, and each adapter calls its closure as the element reaches it. The adapters ask for elements as follows:

- `map` and `filter` call their closures on every element that reaches them;
- `take(n)` asks its source for no element after the `n`th;
- `take_while` asks for none after the first that its closure rejects;
- `skip(n)` and `skip_while` ask and drop;
- `zip` asks `self` and then `other` for each pair, and ends with the first that ends;
- `chain` asks `other` once `self` ends.

A negative `n` counts as 0: `take(n)` then gives no element and asks its source for none, and `skip(n)` drops none.

An iterator is a value: every consumer starts from its first element, and an iterator that no consumer reads runs nothing.

Tests: [views/iterator_negative_counts.lt](../conformance/views/iterator_negative_counts.lt), [views/laziness.lt](../conformance/views/laziness.lt).

<a id="views.consumers"></a>
The **consumers** are native, and are in `impl<T> Iter<T>` unless the list says otherwise. Each reads every element it needs, in order, and calls its callback as the list methods do ([std.callbacks](17-std.md#std.callbacks)). So the callback's effects pass through ([effects.non-escaping-parameters](12-effects.md#effects.non-escaping-parameters)). The consumers are these:

- `collect(self) -> List<T>`;
- `fold<A>(self, init: A, f: fn(A, T) -> A) -> A`;
- `count(self) -> i64`;
- `any(self, p: fn(T) -> bool) -> bool` and `all(self, p: fn(T) -> bool) -> bool`, which stop at the first element that decides them;
- `find(self, p: fn(T) -> bool) -> Option<T>`, `first(self) -> Option<T>`, `last(self) -> Option<T>` and `nth(self, n: i64) -> Option<T>`;
- in `impl<T: Ord> Iter<T>`: `max(self) -> Option<T>` and `min(self) -> Option<T>`, the first of equal elements.

`nth(n)` with a negative `n` is `None`, and reads no element.

A consumer's result is an owned value, so an element of a view type can't be consumed into a `List`: `collect` on an `Iter<View<str>>` is E0421.

Tests: [views/consumer_callback_raises.lt](../conformance/views/consumer_callback_raises.lt), [views/iterator_negative_counts.lt](../conformance/views/iterator_negative_counts.lt), [views/iterators.lt](../conformance/views/iterators.lt), [views/stored.lt](../conformance/views/stored.lt).

<a id="views.iterator-traits"></a>
`Iter<T>` has none of the structural traits ([traits.structural-impls](11-traits.md#traits.structural-impls)): two iterators can't be compared, and one can't be shown (E0318).

Tests: [views/iterators_have_no_traits.lt](../conformance/views/iterators_have_no_traits.lt).

<a id="views.show"></a>
`stilt show` prints a function's views as it prints its modes ([modes.show](#modes.show)). It prints `views line` in the bracket, for a result that views the parameter `line`, at the line of the expression returned. It prints `` `w` views `text` `` at the line of a binding of a view type, naming each source. The word stands for `fixed`, which every view is, so a view binding prints no `fixed`. The facts suite has `VIEWS x`, naming the source `x`, at that line, and a module that names a view type carries `//~ tier: advanced`. What a view reads is no part of a package's API ([versions.facts-in-api](21-versions.md#versions.facts-in-api)).

Checked by: the toolchain's tests of `stilt show` and of the language server's hover (`compiler/stilt-cli/tests/show.rs`, `compiler/stilt-cli/tests/lsp.rs`), and the facts suite, whose `tests/facts/views.lt` `just facts` checks.

## Projections

<a id="projections.declaring-projection"></a>
A function or method whose result type is written `inout T` is a **projection**, for any type `T` (the `result` production, [syntax.projection-results](03-syntax.md#syntax.projection-results)). Only a declared function, a method of an inherent impl, and a method of a trait and its impls can be one. A function type and a closure literal have no `inout` result. A trait method that is a projection is implemented by a projection, and one that isn't is implemented by a function that isn't. An impl's method that differs from the trait's in this is E0307, as any method whose signature isn't the trait's is ([traits.implementing-trait](11-traits.md#traits.implementing-trait)). A module that declares or calls a projection is in the advanced tier ([program.module-tier](04-programs.md#program.module-tier)).

Tests: [ported/hylo_geometry.lt](../conformance/ported/hylo_geometry.lt), [projections/generic_recursive_trait.lt](../conformance/projections/generic_recursive_trait.lt), [projections/projection_basics.lt](../conformance/projections/projection_basics.lt), [projections/trait_projection.lt](../conformance/projections/trait_projection.lt).

<a id="projections.cannot-raise"></a>
A projection's row holds no `raise<E>`: `raise<E>` in it is E0427, *a projection can't raise*, at the element. A call that is a place can't sit in the operand of a `try` ([effects.marking](12-effects.md#effects.marking)). A `raise` in the body is then E0502, as in any function whose row lacks it ([effects.inference](12-effects.md#effects.inference)).

Tests: [projections/cannot_raise.lt](../conformance/projections/cannot_raise.lt), [projections/raise_in_body.lt](../conformance/projections/raise_in_body.lt).

<a id="projections.yield"></a>
`yield e` is a statement, allowed only in the body of a projection. In any other function's body, in a closure literal, a test, a constant or a doc example, it is E0425, *`yield` outside a projection*. Its operand is one of these:

- a place rooted in a `var` binding or an `inout` parameter of the body, of the projection's type `T`;
- an expression of a view type that isn't a place, which is bound by `var` to a temporary of the statement and yielded as that place ([projections.writable-bindings](#projections.writable-bindings)).

Any other operand is E0401, and a place rooted in a `let` binding is E0403 ([modes.what-can-be-modified](#modes.what-can-be-modified)). The operand's index expressions are evaluated when the statement runs, and the place is then handed to the caller. A `yield` whose place goes through an index allocates, as an `inout` argument's does ([facts.allocation](15-facts.md#facts.allocation)), and yielding a binding is where it escapes ([modes.escaping](#modes.escaping)). A projection's body has type `()`: its block's final expression, if any, is `()`, and a `return` in it takes no value.

Tests: [ported/hylo_local_inout.lt](../conformance/ported/hylo_local_inout.lt), [ported/swift_generalized_accessors.lt](../conformance/ported/swift_generalized_accessors.lt), [projections/after_yield.lt](../conformance/projections/after_yield.lt), [projections/bindings.lt](../conformance/projections/bindings.lt), [projections/projection_basics.lt](../conformance/projections/projection_basics.lt), [projections/yield_outside.lt](../conformance/projections/yield_outside.lt), [projections/yield_places.lt](../conformance/projections/yield_places.lt), [verification/order_effects_rejected.lt](../conformance/verification/order_effects_rejected.lt), [verification/order_yielded.lt](../conformance/verification/order_yielded.lt).

<a id="projections.once-on-every-path"></a>
Every path through a projection's body from its start to its end or to a `return` runs exactly one `yield`. A path that ends by raising or panicking runs at most one. Breaking this is E0424, *a projection yields exactly once*, at one of these places:

- a `yield` inside a `loop`, `while` or `for` body, which then counts as the one `yield` of the paths through the loop;
- a `yield` inside the operand of a `try` that has `catch` arms, which then counts as the one `yield` of the paths through it;
- the second `yield` of a path;
- for a path without one, the end of the body, its closing brace, or the `return` the path reaches.

The check is syntactic, as the law of exclusivity is. The paths through the arms of an `if`, a `match` or a `catch` are followed one by one, and an arm whose type is `Never` ends its paths.

Tests: [ported/hylo_projection_yields.lt](../conformance/ported/hylo_projection_yields.lt), [projections/hole_arm.lt](../conformance/projections/hole_arm.lt), [projections/yield_once.lt](../conformance/projections/yield_once.lt), [projections/yield_once_accepted.lt](../conformance/projections/yield_once_accepted.lt).

<a id="projections.call-is-place"></a>
A call of a projection, `f(args)` or `x.m(args)`, is a place of type `T` rooted in the call, which can be modified. The call can be:

- assigned to;
- the target of a compound assignment;
- passed `inout`;
- the receiver of a method that takes `inout self`;
- followed by fields, tuple fields and indexes of its own, which are places too.

For every other use the call is read: the value of the yielded place is copied out, and the projection resumes before the copy is used. Those uses include a `let` binding, an argument to a `let` parameter, an operand, a `for`'s iterable and the argument of `View.of`. So a `for` over a projection's call iterates a copy, and a view of one has a temporary as its source ([views.making-view](#views.making-view)). When `T` is itself a view type, the copy is a view with the sources that [views.across-calls](#views.across-calls) gives a call's result.

Tests: [ported/hylo_geometry.lt](../conformance/ported/hylo_geometry.lt), [ported/hylo_local_inout.lt](../conformance/ported/hylo_local_inout.lt), [ported/swift_generalized_accessors.lt](../conformance/ported/swift_generalized_accessors.lt), [ported/swift_writeback.lt](../conformance/ported/swift_writeback.lt), [projections/copied_out.lt](../conformance/projections/copied_out.lt), [projections/generic_recursive_trait.lt](../conformance/projections/generic_recursive_trait.lt), [projections/projection_basics.lt](../conformance/projections/projection_basics.lt), [projections/reads.lt](../conformance/projections/reads.lt).

<a id="projections.not-a-value"></a>
A projection named other than to call it, as a value, an argument or a stored function, is E0426, *a projection isn't a value*, at the name. A projection has no function type.

Tests: [projections/not_a_value.lt](../conformance/projections/not_a_value.lt).

<a id="projections.when-projection-runs"></a>
A projection's arguments are evaluated where a place's index expressions are ([values.inout-argument-order](05-values.md#values.inout-argument-order), [values.assignment-order](05-values.md#values.assignment-order)). That is in their turn among the arguments of an enclosing call, and before the right-hand side of an assignment. The call starts where the access of the place starts ([modes.durations](#modes.durations)):

- at the store, for an assignment;
- at the start of the enclosing call, for an `inout` argument or an `inout self` receiver;
- where the read happens, for a read.

From there, the call runs in these steps:

1. Its `inout` arguments are read.
2. The body runs to its `yield`.
3. The caller's access happens on the yielded place.
4. The body resumes after the `yield` and runs to its end.
5. The `inout` arguments are written back.

When several arguments of one call are projections' calls, they start from left to right and resume from right to left. Each runs inside the one before it, as nested calls do. The projection's `inout` arguments are modifications, and its `let` arguments reads, for exactly that span, under the law of exclusivity. So `swap(inout g.at(0, 0), inout g.at(1, 1))` is E0402 ([modes.overlapping-inout](#modes.overlapping-inout)), because both calls hold `g`.

Tests: [ported/hylo_local_inout.lt](../conformance/ported/hylo_local_inout.lt), [ported/swift_generalized_accessors.lt](../conformance/ported/swift_generalized_accessors.lt), [ported/swift_writeback.lt](../conformance/ported/swift_writeback.lt), [projections/after_yield.lt](../conformance/projections/after_yield.lt), [projections/order.lt](../conformance/projections/order.lt), [projections/overlap.lt](../conformance/projections/overlap.lt), [projections/projection_basics.lt](../conformance/projections/projection_basics.lt).

<a id="projections.raising-during-access"></a>
The caller's access runs in the caller. Its effects are the caller's, and a `without` on the projection doesn't count them. When the access raises or panics, the projection doesn't resume. The statements after its `yield` don't run, no `catch` of the projection's own sees the error, and the projection's `inout` arguments hold the changes made before the `yield` ([values.inout-arguments](05-values.md#values.inout-arguments)).

Tests: [projections/raising.lt](../conformance/projections/raising.lt).

<a id="projections.nested"></a>
The operand of a `yield` may be a projection's call, and so may a projection's argument. The inner projection stays suspended for as long as the outer one's access lasts, with the same durations ([projections.when-projection-runs](#projections.when-projection-runs)).

Tests: [ported/swift_writeback.lt](../conformance/ported/swift_writeback.lt), [projections/generic_recursive_trait.lt](../conformance/projections/generic_recursive_trait.lt).

## Writable views

<a id="projections.writable-views"></a>
Three native functions of `std.view` make views through `inout`:

- `view.into<U>(inout xs: List<U>, start: i64, end: i64) -> View<List<U>>` views the part of `xs` from `start` up to `end`, and panics with `bounds` as `View.of` does ([views.making-view](#views.making-view));
- `view.part<U>(inout v: View<List<U>>, start: i64, end: i64) -> View<List<U>>` views a part of a view, with offsets counted from the view's start, as `v.view` does;
- `view.split<U>(inout xs: List<U>, at: i64, f: fn(inout View<List<U>>, inout View<List<U>>))` calls `f` once with the parts of `xs` before and from `at`, each writable. It panics with `bounds` unless `0 ≤ at ≤ xs.len()`. `f` is a non-escaping parameter, so its effects pass through ([effects.non-escaping-parameters](12-effects.md#effects.non-escaping-parameters)).

Views of strings are read-only. `into` and `split` make the storage of `xs` unique where it is shared, as a write to it would. That is the only work they do, and each allocates, as an assignment through an index does ([facts.allocation](15-facts.md#facts.allocation)). `part` doesn't allocate, since the storage that a writable binding writes is unique already.

Tests: [ported/swift_arrays.lt](../conformance/ported/swift_arrays.lt), [projections/into_bounds.lt](../conformance/projections/into_bounds.lt), [projections/part_bounds.lt](../conformance/projections/part_bounds.lt), [projections/part_past_view.lt](../conformance/projections/part_past_view.lt), [projections/split.lt](../conformance/projections/split.lt), [projections/split_bounds.lt](../conformance/projections/split_bounds.lt), [projections/writable_views.lt](../conformance/projections/writable_views.lt).

<a id="projections.what-view-writes"></a>
A view **writes** each source that it is made from through `inout`: `view.into(inout xs, …)` writes `xs`, and `view.part(inout v, …)` writes `v`. The result of a call whose result type is a view type writes every argument passed `inout` whose type is viewable or a view type, and views the others ([views.across-calls](#views.across-calls)). An `inout` argument that is a projection's call is a temporary that lasts as long as the view. A writable binding ([projections.writable-bindings](#projections.writable-bindings)) holds what its view writes as a modification of it ([modes.kinds-of-access](#modes.kinds-of-access)) for the binding's scope. Any other binding, and a view that no binding holds, holds its sources as reads for the durations of [views.reads-that-last](#views.reads-that-last), whatever its view writes. So `let w = view.into(inout xs, 0, 1)` reads `xs`.

Tests: [projections/bindings_accepted.lt](../conformance/projections/bindings_accepted.lt), [projections/copied_out.lt](../conformance/projections/copied_out.lt), [projections/writing_accepted.lt](../conformance/projections/writing_accepted.lt).

<a id="projections.reaching-written-source"></a>
While a writable binding writes a source, any access to a place that overlaps the source is E0429, *reaching a value while a view writes it*, at the access. A read is such an access too. This is the law of exclusivity, applied to the binding's write. The error names the view and the line where its write ends. It is counted as E0404 is ([modes.change-while-iterating](#modes.change-while-iterating)). The error offers two fixes: reach the value before the view, or end the view's binding's scope first.

Tests: [projections/writing.lt](../conformance/projections/writing.lt), [projections/writing_accepted.lt](../conformance/projections/writing_accepted.lt).

<a id="projections.writable-bindings"></a>
A `var` binding of type `View<T>`, and an `inout` parameter of type `View<T>`, are **writable**. A binding of `Option<View<T>>` reads, as other bindings do, since no place goes through an `Option`. The view given to a `var` binding, as its value or assigned to the whole of it, must write every source it has. Given to a `var` binding or to the `var` of a `yield` ([projections.yield](#projections.yield)), a view that reads a source is E0428, *a view reads what it must write*. The error is at the view, and names the source. The error offers two fixes: make the view with `view.into(inout xs, …)`, or bind it with `let`. An `inout` argument is a place, so it is a writable binding already, which writes itself inside the callee.

Tests: [projections/bindings.lt](../conformance/projections/bindings.lt), [projections/bindings_accepted.lt](../conformance/projections/bindings_accepted.lt).

<a id="projections.places-through-views"></a>
For a binding `v` of type `View<List<U>>`, `v[i]` is a place rooted in `v` ([modes.places](#modes.places)). When `v` is writable, `v[i]` can be assigned to, passed `inout` and be the receiver of a method with `inout self`. Otherwise modifying it is E0403, as for any place rooted in a `let` binding. `v[i]` panics with `bounds` as a read of `v[i]` does ([views.functions-of-views](#views.functions-of-views)). A write through it doesn't allocate, since the storage a writable binding writes is unique. A writable binding is a source in its own right. A view made from it, by `v.view(…)`, `view.part(inout v, …)` or `Iter.of_view(v)`, has `v` as its source, not what `v` writes. So a change through `v` while such a view lives is E0423, and reaching what `v` writes is only ever E0429.

Tests: [ported/swift_arrays.lt](../conformance/ported/swift_arrays.lt), [projections/bindings.lt](../conformance/projections/bindings.lt), [projections/bindings_accepted.lt](../conformance/projections/bindings_accepted.lt), [projections/view_index_bounds.lt](../conformance/projections/view_index_bounds.lt), [projections/writable_views.lt](../conformance/projections/writable_views.lt).

<a id="projections.results-that-write"></a>
A view in a function's result, or yielded by a projection, may have an `inout` parameter among its sources only when it writes it. One that reads an `inout` parameter of a viewable or view type is E0428, at the view, naming the parameter, with the fix `view.into(inout xs, …)`. A view in a result of a local, of a `let` parameter that isn't viewable, or captured by an escaping closure, is E0422 ([views.escaping](#views.escaping)). A caller reads such a result as [projections.what-view-writes](#projections.what-view-writes) says: it writes the arguments passed `inout` and views the others. So `var h = f(inout xs)` is accepted when `xs` is the one argument `f` could view. `var h = f(inout xs, ys)` is E0428, because the result views `ys`.

Tests: [projections/copied_out.lt](../conformance/projections/copied_out.lt), [projections/results.lt](../conformance/projections/results.lt), [projections/results_accepted.lt](../conformance/projections/results_accepted.lt), [views/escaping.lt](../conformance/views/escaping.lt).

<a id="projections.writable-modes"></a>
A writable binding is `fixed`, as every binding of a view type is ([views.fixed](#views.fixed)). `stilt show` prints `writes` for it, which stands for `fixed` as `views` does. A write through a view is a modification of the view's binding, not of what it writes, so no binding is `shared` for it ([modes.shared-writes](#modes.shared-writes)).

Checked by: the facts suite, whose `tests/facts/projections.lt` gives `WRITES x`, which stands for `fixed`, and which `just facts` checks, and the toolchain's tests of `stilt show`.

<a id="projections.show"></a>
`stilt show` prints `` `tail` writes `xs` `` at the line of a writable binding, naming each source it writes. It prints `` `w` views `tail` `` for a view whose source is a writable binding. A projection's signature prints `-> inout T` as written, and nothing else is printed for it. The facts suite has `WRITES x` at the line of a writable binding. `stilt fmt` prints `-> inout T` and `yield e` as the grammar writes them, and `yield e` is `(yield E)` in the syntax tree ([syntax.tree-form](03-syntax.md#syntax.tree-form)). What a binding writes is no part of a package's API ([versions.facts-in-api](21-versions.md#versions.facts-in-api)).

Checked by: the toolchain's tests of `stilt show` (`compiler/stilt-cli/tests/show.rs`), the facts suite, whose `tests/facts/projections.lt` `just facts` checks, and the formatter's pair `tests/format/projections` (`compiler/stilt-fmt/tests/formatting.rs`).
