# 8. Expressions

This chapter gives the forms of a body, and how each is checked and evaluated:

- statements and blocks;
- the operators, their precedence, and how a binary operation is checked;
- struct literals, and the heads of control-flow forms;
- closures, key paths and calls;
- the `else` fallback, `if`, `if let`, `match` and loops;
- assignment, places, conditions and scope.

The grammar is in [Syntax](03-syntax.md), evaluation order and copies are in [The value model](05-values.md), inference is in [Types and generics](07-types.md), and matching is in [Patterns](09-patterns.md).

## Statements and blocks

<a id="expressions.statements"></a>
A statement is one of these:

- a `let` or a `var`;
- an assignment or a compound assignment;
- an `assert` ([program.assert-expr](04-programs.md#program.assert-expr));
- a `yield`, in a projection's body ([projections.yield](13-modes.md#projections.yield));
- an **expression statement**, which is an expression in statement position.

Tests: [expressions/assignment_in_condition.lt](../conformance/expressions/assignment_in_condition.lt), [expressions/assignment_not_expression.lt](../conformance/expressions/assignment_not_expression.lt), [ported/hanoi.lt](../conformance/ported/hanoi.lt).

<a id="expressions.block-value"></a>
A block holds statements, separated as [lexical.separators](02-lexical.md#lexical.separators) describes. It evaluates to its last statement when that is an expression statement, and to `()` otherwise.

Tests: [expressions/block_final_expression.lt](../conformance/expressions/block_final_expression.lt), [expressions/block_values.lt](../conformance/expressions/block_values.lt), [lexical/brackets_on_next_line.lt](../conformance/lexical/brackets_on_next_line.lt), [lexical/hole_dot_starts_line.lt](../conformance/lexical/hole_dot_starts_line.lt), [lexical/logical_or_starts_line.lt](../conformance/lexical/logical_or_starts_line.lt), [lexical/minus_starts_line.lt](../conformance/lexical/minus_starts_line.lt).

<a id="expressions.unused-values"></a>
An expression statement that isn't the last statement of its block must have type `()` or `Never`. Any other type there is E0322, *unused value*. So `xs.sorted()` on its own line, which returns a new list and changes nothing, is an error. `let _ = e` discards a value on purpose. A loop's body discards its value, so its last expression statement is held to the same rule.

Tests: [expressions/loop_body_value.lt](../conformance/expressions/loop_body_value.lt), [expressions/unused_values.lt](../conformance/expressions/unused_values.lt), [types/unused_value.lt](../conformance/types/unused_value.lt).

## Operators and precedence

<a id="expressions.precedence"></a>
Operators bind as this table says, from tightest to loosest:

| Level | Forms | Associativity |
| --- | --- | --- |
| 1 | Primary: literals, names, `(…)`, tuples, `[…]`, struct and record literals, blocks, `if`, `match`, `loop`, `while`, `for`, closures, key paths, holes `?` ([declarations.typed-holes](10-declarations.md#declarations.typed-holes)), and the other forms of the `primary` production | |
| 2 | Postfix: call `f(…)`, field `.x`, tuple field `.0`, method call `.m(…)`, index `[i]` | left |
| 3 | Prefix `-` `!` | right |
| 4 | `*` `/` `%` `*%` | left |
| 5 | `+` `-` `+%` `-%` | left |
| 6 | `<<` `>>` | left |
| 7 | `&` | left |
| 8 | `^` | left |
| 9 | `\|` | left |
| 10 | `==` `!=` `<` `<=` `>` `>=` | none |
| 11 | `&&` | left |
| 12 | `\|\|` | left |
| 13 | `else`, the `Option` fallback | right |
| 14 | `try e`, `try e catch …`, `raise e`, `return` with or without an operand, `break`, `continue`, closure bodies | prefix |

Comparisons don't chain, so `a < b < c` is a syntax error (E0100). The `expr` production ([syntax.expressions](03-syntax.md#syntax.expressions)) follows this table.

Tests: [expressions/chained_comparison.lt](../conformance/expressions/chained_comparison.lt), [expressions/precedence_levels.lt](../conformance/expressions/precedence_levels.lt), [expressions/question_mark_operator.lt](../conformance/expressions/question_mark_operator.lt).

<a id="expressions.open-ended-forms"></a>
The operand of a level-14 form extends as far right as possible, except that the operand of `try` stops before `catch`. A level-14 form may also be the operand of a prefix operator, or the right operand of any binary operator or of `else`. Its operand then extends as far right as possible too. So `x else raise e + 1` means `x else (raise (e + 1))`.

Tests: [expressions/precedence_levels.lt](../conformance/expressions/precedence_levels.lt), [expressions/return_in_head.lt](../conformance/expressions/return_in_head.lt).

<a id="expressions.catch-attachment"></a>
A `catch` belongs to the innermost `try` whose operand is still open where the `catch` appears ([effects.catch-syntax](12-effects.md#effects.catch-syntax)). So in `try a(try b()) catch …`, it belongs to the outer `try`, because the inner operand closed at `)`. In `try a + try b() catch …`, it belongs to the inner one.

Tests: [expressions/catch_binding.lt](../conformance/expressions/catch_binding.lt).

<a id="expressions.trailing-commas"></a>
Every comma-separated list may end with a comma. That holds for arguments, parameters, generics, type arguments, tuple and list elements, fields, payloads, the elements of patterns, `..` included, and the elements of rows. In parentheses, one element followed by a comma is a one-element tuple, `(e,)`, while `(e)` is `e`.

Tests: [expressions/trailing_commas.lt](../conformance/expressions/trailing_commas.lt).

<a id="expressions.ranges"></a>
Ranges are not values. `a..b` and `a..=b` appear only as the iterable of a `for` ([expressions.range-iteration](#expressions.range-iteration)). Anywhere else they are a syntax error (E0100). `..` and `..=` bind more loosely than every operator, so `0..n + 1` means `0..(n + 1)`.

Tests: [expressions/range_outside_for.lt](../conformance/expressions/range_outside_for.lt), [expressions/ranges.lt](../conformance/expressions/ranges.lt).

## How an operation is checked

<a id="expressions.left-operand-first"></a>
A binary operator checks its left operand first. If the left operand's type is known and the operator isn't defined on it ([Numbers](06-numbers.md)), the operation is E0317, *operator not defined on a type*. The right operand is then checked alone, with no expected type. So `"total: " + n` is E0317, with the fix of [expressions.no-string-plus](#expressions.no-string-plus), whatever the type of `n`. On a type that isn't numeric, `==`, `!=` and the ordering operators are defined through `Eq` and `Ord` ([traits.prelude-traits](11-traits.md#traits.prelude-traits)). So on a type without the impl, they are E0318, not E0317, as `<` on a `Map` is.

Tests: [types/operator_undefined_on_left.lt](../conformance/types/operator_undefined_on_left.lt), [types/operators_on_option.lt](../conformance/types/operators_on_option.lt).

<a id="expressions.right-operand"></a>
Otherwise, including when the left operand's type isn't known yet, the right operand is checked as the operator requires. For arithmetic, bitwise operators and comparisons, the expected type is the left operand's type ([numbers.no-implicit-conversions](06-numbers.md#numbers.no-implicit-conversions), [numbers.comparisons](06-numbers.md#numbers.comparisons)). A mismatch is E0311 at the right operand, so `x * 2.0` with `x: i64` is an error at `2.0`. For `&&` and `||`, the expected type is `bool`. A shift's amount is checked as [numbers.shift-amounts](06-numbers.md#numbers.shift-amounts) says.

Tests: [types/operator_mismatch_on_two_lines.lt](../conformance/types/operator_mismatch_on_two_lines.lt), [types/operator_right_mismatch.lt](../conformance/types/operator_right_mismatch.lt).

<a id="expressions.logical-operands"></a>
`&&` and `||` are defined only on `bool`, and both operands are checked against `bool` ([expressions.conditions](#expressions.conditions)). So an operand of another type is E0311 at that operand, never E0317. `x && true` with `x: i64` is an error at `x`, and `1 && x` is two errors.

Tests: [types/logical_operand_not_bool.lt](../conformance/types/logical_operand_not_bool.lt).

<a id="expressions.mismatch-first"></a>
A comparison whose right operand is a type mismatch needs no `Eq` or `Ord`, so `m < 1` with `m: Map<str, i64>` is only E0311, at `1`.

Tests: [types/comparison_mismatch_first.lt](../conformance/types/comparison_mismatch_first.lt).

<a id="expressions.open-left-operand"></a>
When the left operand's type isn't known yet, as an open literal's isn't, whether the operator is defined is checked once the body's types are decided. An operator that isn't defined then is E0317 at the operation. The right operand is checked first. So `1 + "a"` is E0311 at `"a"`, because an integer literal is never a `str` ([numbers.integer-literals](06-numbers.md#numbers.integer-literals)).

Tests: [types/operator_open_left.lt](../conformance/types/operator_open_left.lt), [types/operator_open_left_undefined.lt](../conformance/types/operator_open_left_undefined.lt).

<a id="expressions.no-string-plus"></a>
`+` is not defined on `str` (E0317). Strings are built with interpolation ([lexical.interpolation](02-lexical.md#lexical.interpolation)). The error for `a + b` offers the fix `"{a}{b}"`.

Tests: [checking/operator_error_once.lt](../conformance/checking/operator_error_once.lt), [expressions/string_building.lt](../conformance/expressions/string_building.lt), [expressions/string_plus.lt](../conformance/expressions/string_plus.lt), [types/operator_undefined_on_left.lt](../conformance/types/operator_undefined_on_left.lt), [types/operators.lt](../conformance/types/operators.lt).

<a id="expressions.indexing"></a>
Only lists and maps ([std.lists](17-std.md#std.lists), [std.maps](17-std.md#std.maps)), arrays ([generics.array-elements](07-types.md#generics.array-elements)) and views of lists ([views.functions-of-views](13-modes.md#views.functions-of-views)) can be indexed. Indexing a value of any other type, as `s[0]` on a `str`, is E0317.

Tests: [std/string_index.lt](../conformance/std/string_index.lt).

## Struct literals and heads

<a id="expressions.struct-literals"></a>
Outside a head ([expressions.heads](#expressions.heads)), `e {` begins a **struct literal**. `e` must be an uppercase identifier ([lexical.case](02-lexical.md#lexical.case)), `Self`, or a path of identifiers joined by `.` that ends in an uppercase one, as `orders.Order` is. A `{` directly after any other expression is a syntax error (E0100). So `f() { x: 1 }`, `(A) { x: 1 }` and `Self.X { x: 1 }` are rejected.

Tests: [expressions/qualified_struct_literal](../conformance/expressions/qualified_struct_literal/), [expressions/struct_after_call.lt](../conformance/expressions/struct_after_call.lt), [expressions/struct_after_parens.lt](../conformance/expressions/struct_after_parens.lt), [expressions/struct_after_self_path.lt](../conformance/expressions/struct_after_self_path.lt), [expressions/struct_literal_forms.lt](../conformance/expressions/struct_literal_forms.lt), [expressions/struct_lowercase_name.lt](../conformance/expressions/struct_lowercase_name.lt).

<a id="expressions.struct-literal-fields"></a>
A struct literal's fields are written `Name { f: e, g }`, where a bare `g` is short for `g: g`. Every field of the record must be given exactly once (E0316), and a field that the record doesn't have is E0313. `Name { ..base, f: e }` gives some fields and copies the others from `base` ([records.update](07-types.md#records.update)).

Tests: [expressions/field_punning.lt](../conformance/expressions/field_punning.lt), [expressions/record_literal_fields.lt](../conformance/expressions/record_literal_fields.lt), [expressions/struct_literal_forms.lt](../conformance/expressions/struct_literal_forms.lt), [ported/knapsack.lt](../conformance/ported/knapsack.lt), [types/fields.lt](../conformance/types/fields.lt), [values/evaluation_order.lt](../conformance/values/evaluation_order.lt).

<a id="expressions.heads"></a>
The head of an `if`, a `while` or a `match` ends at the first `{` that isn't inside parentheses or brackets. So does the iterable of a `for`. That `{` always opens the body. So `if x == None {` and `while n < MAX {` mean what they say. A head's grammar is the `head` production ([syntax.heads](03-syntax.md#syntax.heads)).

Tests: [expressions/bracketed_heads.lt](../conformance/expressions/bracketed_heads.lt), [expressions/parenthesized_heads.lt](../conformance/expressions/parenthesized_heads.lt), [expressions/return_in_head.lt](../conformance/expressions/return_in_head.lt).

<a id="expressions.head-contents"></a>
A head that holds one of these outside parentheses and brackets is a syntax error (E0100):

- a block, an `if`, a `match`, a `loop`, a `while` or a `for`;
- a struct or record literal;
- the block form of `catch`;
- one of the other forms that end in a block, which the `head` production leaves out ([syntax.heads](03-syntax.md#syntax.heads)).

Wrapped in parentheses, all of these are allowed, as in `if p == (Point { x: 0, y: 0 }) {`.

Tests: [expressions/head_block.lt](../conformance/expressions/head_block.lt), [expressions/head_catch_block.lt](../conformance/expressions/head_catch_block.lt), [expressions/head_for.lt](../conformance/expressions/head_for.lt), [expressions/head_if.lt](../conformance/expressions/head_if.lt), [expressions/head_loop.lt](../conformance/expressions/head_loop.lt), [expressions/head_match.lt](../conformance/expressions/head_match.lt), [expressions/head_struct_literal.lt](../conformance/expressions/head_struct_literal.lt), [expressions/head_while.lt](../conformance/expressions/head_while.lt), [expressions/parenthesized_heads.lt](../conformance/expressions/parenthesized_heads.lt).

## Closures

<a id="expressions.closures"></a>
A **closure** is written `|p₁, …, pₙ| body`, or `|| body` when it takes no parameters. Its parameters are irrefutable patterns ([patterns.irrefutable-positions](09-patterns.md#patterns.irrefutable-positions)), and may carry type annotations, as in `|x: i64| x + 1`. Its body extends as far right as possible. Its return type is inferred from its body. A closure has no return-type annotation, so `|x: i64| -> i64 { x }` is a syntax error (E0100).

Tests: [expressions/bar_token.lt](../conformance/expressions/bar_token.lt), [expressions/closure_forms.lt](../conformance/expressions/closure_forms.lt), [expressions/closure_return_annotation.lt](../conformance/expressions/closure_return_annotation.lt), [patterns/irrefutable_positions.lt](../conformance/patterns/irrefutable_positions.lt), [patterns/refutable_patterns.lt](../conformance/patterns/refutable_patterns.lt), [values/closure_copies.lt](../conformance/values/closure_copies.lt).

<a id="expressions.closure-parameter-types"></a>
A closure parameter's type comes from the expected function type, or from an annotation on the parameter. A parameter with neither gets its type from the body by inference ([types.expected-types](07-types.md#types.expected-types)). So `|x| x * rate` takes the type of `rate`, while a method call on such a parameter is E0312, which asks for an annotation ([types.known-types](07-types.md#types.known-types)). A closure must take as many parameters as the function type expected of it has (E0315).

Tests: [expressions/closure_parameter_from_body.lt](../conformance/expressions/closure_parameter_from_body.lt), [expressions/closure_parameter_method.lt](../conformance/expressions/closure_parameter_method.lt), [types/argument_counts.lt](../conformance/types/argument_counts.lt).

<a id="expressions.inout-closure-parameters"></a>
A closure parameter may be marked `inout`, as in `|inout b| …` or `|inout b: Body| …`. Such a parameter is a name, not a pattern, so `|inout (a, b)|` is a syntax error (E0100). The closure's type has an `inout` parameter there ([declarations.function-types](10-declarations.md#declarations.function-types)). Its type comes from the expected function type or the annotation, as any parameter's does. The closure changes the caller's place through it, as a function does through its `inout` parameter. The parameter isn't a capture, so [expressions.capture](#expressions.capture) doesn't apply to it, and the closure still can't modify what it captures.

Tests: [expressions/closure_inout_captures.lt](../conformance/expressions/closure_inout_captures.lt), [expressions/closure_inout_in_list.lt](../conformance/expressions/closure_inout_in_list.lt), [expressions/closure_inout_not_a_pattern.lt](../conformance/expressions/closure_inout_not_a_pattern.lt), [expressions/closure_inout_parameters.lt](../conformance/expressions/closure_inout_parameters.lt), [expressions/closure_inout_raise.lt](../conformance/expressions/closure_inout_raise.lt), [expressions/closure_inout_unmarked.lt](../conformance/expressions/closure_inout_unmarked.lt), [properties/inout_parameter.lt](../conformance/properties/inout_parameter.lt), [types/nested_function_types.lt](../conformance/types/nested_function_types.lt).

<a id="expressions.bar-token"></a>
At the start of an operand, `|` or `||` begins a closure. After an operand, `|` means bitwise or and `||` means logical or. In a pattern, `|` separates alternatives ([patterns.pattern-forms](09-patterns.md#patterns.pattern-forms)).

Tests: [expressions/bar_token.lt](../conformance/expressions/bar_token.lt), [expressions/closure_forms.lt](../conformance/expressions/closure_forms.lt).

<a id="expressions.capture"></a>
A closure captures the variables it uses by copy, at the moment it is created ([values.independent-copies](05-values.md#values.independent-copies)). Modifying a captured variable inside the closure is E0403, whether by assignment or by passing it as an `inout` argument or receiver ([modes.closures](13-modes.md#modes.closures)).

Tests: [expressions/closure_captures_at_creation.lt](../conformance/expressions/closure_captures_at_creation.lt), [expressions/closure_inout_captures.lt](../conformance/expressions/closure_inout_captures.lt), [expressions/closure_modifies_capture.lt](../conformance/expressions/closure_modifies_capture.lt), [modes/read_only_bindings.lt](../conformance/modes/read_only_bindings.lt), [modes/shared_storage_read_after.lt](../conformance/modes/shared_storage_read_after.lt), [modes/unmodifiable_takes_no_part.lt](../conformance/modes/unmodifiable_takes_no_part.lt), [ported/effekt_abort_past_var.lt](../conformance/ported/effekt_abort_past_var.lt), [values/closure_copies.lt](../conformance/values/closure_copies.lt), [values/passed_then_captured.lt](../conformance/values/passed_then_captured.lt).

<a id="expressions.closure-boundaries"></a>
`return` inside a closure returns from the closure. `break` and `continue` can't cross a closure's boundary (E0216, [expressions.break-and-continue](#expressions.break-and-continue)). A closure can't call itself. The `let` that names it takes effect only after its statement ([expressions.scope](#expressions.scope)), so in its own body its name is unknown (E0211) or names an earlier binding.

Tests: [expressions/break_across_closure.lt](../conformance/expressions/break_across_closure.lt), [expressions/closure_recursion.lt](../conformance/expressions/closure_recursion.lt), [expressions/closure_return.lt](../conformance/expressions/closure_return.lt), [expressions/if_let_loops.lt](../conformance/expressions/if_let_loops.lt).

## Key paths

<a id="expressions.key-paths"></a>
A **key path** is `.` followed by a chain of field accesses, tuple fields, indexing and method calls, as in `.1`, `.paid`, `.items[0]` or `.name.len()`. The chain starts with a field, a tuple field or a method call, and indexing may follow any of them. A key path `K` means `|x| xK`, so `.paid` means `|x| x.paid`. A key path is allowed only where a function type `fn(T) -> U` is expected. Anywhere else it is E0324, *key path where no function is expected*. The arguments and indexes in the chain are expressions of their own, so `.items.map(.price)` holds a second key path. A key path's fields read through an `Option` as any field does ([types.option-key-paths](07-types.md#types.option-key-paths)).

Tests: [expressions/fields_through_options_key_paths.lt](../conformance/expressions/fields_through_options_key_paths.lt), [expressions/key_path_annotated.lt](../conformance/expressions/key_path_annotated.lt), [expressions/key_path_arguments.lt](../conformance/expressions/key_path_arguments.lt), [expressions/key_path_forms.lt](../conformance/expressions/key_path_forms.lt), [expressions/key_path_without_function.lt](../conformance/expressions/key_path_without_function.lt), [lexical/leading_dot_not_a_float.lt](../conformance/lexical/leading_dot_not_a_float.lt), [ported/pascal.lt](../conformance/ported/pascal.lt), [std/filter_map.lt](../conformance/std/filter_map.lt), [std/filter_map_rejected.lt](../conformance/std/filter_map_rejected.lt), [std/option_filter.lt](../conformance/std/option_filter.lt), [types/key_paths.lt](../conformance/types/key_paths.lt).

## Calls

<a id="expressions.arguments"></a>
Arguments are positional, and a call must give one argument for each parameter (E0315). There are no named arguments, no default values and no variadic functions. So `area(w: 2.0, h: 2.0)` is a syntax error (E0100).

Tests: [declarations/default_parameter.lt](../conformance/declarations/default_parameter.lt), [expressions/argument_counts.lt](../conformance/expressions/argument_counts.lt), [expressions/named_argument.lt](../conformance/expressions/named_argument.lt), [expressions/named_argument_with_equals.lt](../conformance/expressions/named_argument_with_equals.lt), [expressions/positional_arguments.lt](../conformance/expressions/positional_arguments.lt), [reflection/shape_called_with_an_argument.lt](../conformance/reflection/shape_called_with_an_argument.lt), [types/argument_counts.lt](../conformance/types/argument_counts.lt), [types/independent_errors.lt](../conformance/types/independent_errors.lt).

<a id="expressions.inout-arguments"></a>
An argument to an `inout` parameter must be marked `inout` at the call site, as in `normalize(inout v)`, and an argument to any other parameter must not be (E0400). The receiver of a method whose `self` is `inout` is not marked. Both must be places ([expressions.places](#expressions.places)), so `bump(inout 5)` and `[3, 1, 2].push(4)` are E0401.

Tests: [expressions/closure_inout_in_list.lt](../conformance/expressions/closure_inout_in_list.lt), [expressions/closure_inout_parameters.lt](../conformance/expressions/closure_inout_parameters.lt), [expressions/closure_inout_raise.lt](../conformance/expressions/closure_inout_raise.lt), [expressions/closure_inout_unmarked.lt](../conformance/expressions/closure_inout_unmarked.lt), [expressions/inout_function_values.lt](../conformance/expressions/inout_function_values.lt), [expressions/inout_marking_values.lt](../conformance/expressions/inout_marking_values.lt), [modes/inout_marking.lt](../conformance/modes/inout_marking.lt), [modes/inout_marks_in_phase_one.lt](../conformance/modes/inout_marks_in_phase_one.lt), [modes/places.lt](../conformance/modes/places.lt), [traits/qualified_calls.lt](../conformance/traits/qualified_calls.lt), [types/failed_shapes.lt](../conformance/types/failed_shapes.lt), [values/inout_on_raise.lt](../conformance/values/inout_on_raise.lt).

<a id="expressions.consumed-arguments"></a>
An argument is written the same whether the callee consumes it or only reads it ([values.passing-values](05-values.md#values.passing-values)). No mark shows which, and `let` is never written in a call, so `grown(let xs)` is a syntax error (E0100).

Tests: [expressions/inout_marking_values.lt](../conformance/expressions/inout_marking_values.lt), [expressions/let_marked.lt](../conformance/expressions/let_marked.lt), [modes/used_after_passing.lt](../conformance/modes/used_after_passing.lt).

## The `else` fallback

<a id="expressions.option-fallback"></a>
`e₁ else e₂` requires `e₁` to have type `Option<T>`, and `e₂` to have type `T` or `Never` (E0311). Its value is the value inside a `Some`, and `e₂` is evaluated only when `e₁` is `None`. A `Result` must be converted with `.ok()` first.

Tests: [expressions/else_fallback.lt](../conformance/expressions/else_fallback.lt), [expressions/else_fallback_types.lt](../conformance/expressions/else_fallback_types.lt), [expressions/fallback_on_plain_field.lt](../conformance/expressions/fallback_on_plain_field.lt), [expressions/fields_through_options_fallback.lt](../conformance/expressions/fields_through_options_fallback.lt), [expressions/if_let_head_fallback.lt](../conformance/expressions/if_let_head_fallback.lt), [patterns/else_through_tuple](../conformance/patterns/else_through_tuple/), [patterns/let_else.lt](../conformance/patterns/let_else.lt), [patterns/let_else_errors.lt](../conformance/patterns/let_else_errors.lt), [types/failed_shapes.lt](../conformance/types/failed_shapes.lt), [types/mismatched_types.lt](../conformance/types/mismatched_types.lt), [types/never_converts.lt](../conformance/types/never_converts.lt).

<a id="expressions.else-after-if"></a>
An `else` that directly follows the block of an `if` belongs to that `if`. It must be followed by `{` or by `if` (E0100).

Tests: [expressions/else_after_if.lt](../conformance/expressions/else_after_if.lt), [expressions/if_else_chains.lt](../conformance/expressions/if_else_chains.lt), [expressions/if_let_chains.lt](../conformance/expressions/if_let_chains.lt).

<a id="expressions.let-else"></a>
In `let P = e else x`, or `var P = e else x`, with a refutable `P`, `else` makes a let-else ([patterns.let-else](09-patterns.md#patterns.let-else)), not the fallback.

Tests: [expressions/else_fallback.lt](../conformance/expressions/else_fallback.lt), [expressions/else_fallback_types.lt](../conformance/expressions/else_fallback_types.lt), [patterns/let_else.lt](../conformance/patterns/let_else.lt).

## Control flow

<a id="expressions.if"></a>
Without an `else`, the block of `if c { … }` must have type `()` or `Never` (E0323), and the `if` has type `()`. With an `else`, both branches must have a common type, and a branch of type `Never` agrees with any type. Without an expected type, the first branch whose type isn't `Never` sets the common type. The other branch is checked against it ([types.expected-types](07-types.md#types.expected-types)), so a mismatch is reported in that branch. The condition of an `if` may also be a bound test ([meta.bound-tests](16-meta.md#meta.bound-tests)), and an `if` may carry a staging annotation ([meta.staging-annotations](16-meta.md#meta.staging-annotations)).

Tests: [expressions/if_branches.lt](../conformance/expressions/if_branches.lt), [expressions/if_else_chains.lt](../conformance/expressions/if_else_chains.lt), [expressions/if_never_branch.lt](../conformance/expressions/if_never_branch.lt), [types/if_without_else.lt](../conformance/types/if_without_else.lt).

<a id="expressions.if-let"></a>
`if let P = e { … }` matches the value of `e` against the pattern `P`, which may be refutable ([patterns.pattern-forms](09-patterns.md#patterns.pattern-forms)). It takes an optional `else`, as [expressions.else-after-if](#expressions.else-after-if) gives it. When `P` matches, the names it binds are visible in the first block, which runs. Otherwise the `else` runs, or nothing when there is none. Typing is as for `if`, with the bindings in scope in the first block only, and `else if let` chains as `else if` does. There are no conditions joined to a `let` with `&&`, and no `while let`: a loop writes `let P = e else break` inside `loop`.

Tests: [expressions/if_let.lt](../conformance/expressions/if_let.lt), [expressions/if_let_chains.lt](../conformance/expressions/if_let_chains.lt), [expressions/if_let_scope.lt](../conformance/expressions/if_let_scope.lt), [expressions/if_let_types.lt](../conformance/expressions/if_let_types.lt), [patterns/bare_variant_if_let](../conformance/patterns/bare_variant_if_let/).

<a id="expressions.if-let-matching"></a>
`e` is a head ([expressions.heads](#expressions.heads)), so an `else` before the first block is the fallback inside `e` ([expressions.option-fallback](#expressions.option-fallback)). The `let` of an `if let` is no statement, and [expressions.let-else](#expressions.let-else) doesn't apply to it. So `if let Some(x) = a else b {` matches `a else b`. `e` is evaluated once, then matched as a `match` arm would be ([patterns.match](09-patterns.md#patterns.match)). What an `if let` performs, and the accesses it makes ([modes.kinds-of-access](13-modes.md#modes.kinds-of-access)), are those of a `match` with its one arm and a wildcard. An `if let` is never an error of exhaustiveness, and its pattern is never reported as an arm that can't match ([patterns.non-exhaustive-matches](09-patterns.md#patterns.non-exhaustive-matches), [patterns.unreachable-arms](09-patterns.md#patterns.unreachable-arms)).

Tests: [expressions/if_let_hole.lt](../conformance/expressions/if_let_hole.lt), [expressions/if_let_loops.lt](../conformance/expressions/if_let_loops.lt).

<a id="expressions.if-let-always"></a>
An `if let` whose pattern matches every value of the type of `e`, as [patterns.algorithm](09-patterns.md#patterns.algorithm) decides it for a `match` of that one arm, always runs its first block: its `else` never runs, and a `let` says the same. It gets the warning W0303, *`if let` that always matches*, at its pattern, unless the pattern holds a constant ([patterns.guards-and-constants](09-patterns.md#patterns.guards-and-constants)) or `e` has the error type ([errors.error-type](18-errors.md#errors.error-type)). So `if let x = xs.first() { … }` gets it, binding the `Option` itself, where `if let Some(x) = xs.first() { … }` binds what it holds.

Tests: [checking/error_type_in_try_and_match.lt](../conformance/checking/error_type_in_try_and_match.lt), [expressions/if_let_always_matches.lt](../conformance/expressions/if_let_always_matches.lt).

<a id="expressions.match"></a>
In `match e { arms }`, each arm has the form `pattern (if guard)? => expr`. Arms are separated by terminators or commas: two arms with neither between them are a syntax error (E0100). [patterns.match](09-patterns.md#patterns.match) gives matching itself. A `match` may carry a staging annotation ([meta.staging-annotations](16-meta.md#meta.staging-annotations)).

Tests: [expressions/branch_blocks.lt](../conformance/expressions/branch_blocks.lt), [expressions/match_arms.lt](../conformance/expressions/match_arms.lt), [expressions/match_arms_unseparated.lt](../conformance/expressions/match_arms_unseparated.lt), [lexical/arm_separators.lt](../conformance/lexical/arm_separators.lt), [patterns/match_arms.lt](../conformance/patterns/match_arms.lt).

<a id="expressions.loops"></a>
The loops are `while c { … }`, `loop { … }` and `for p in e { … }`. A `for` may carry a staging annotation ([meta.staging-annotations](16-meta.md#meta.staging-annotations)).

Tests: [expressions/loop_forms.lt](../conformance/expressions/loop_forms.lt), [modes/bound_in_loops.lt](../conformance/modes/bound_in_loops.lt), [ported/effekt_loops.lt](../conformance/ported/effekt_loops.lt), [ported/ethiopian_multiplication.lt](../conformance/ported/ethiopian_multiplication.lt), [ported/hailstone.lt](../conformance/ported/hailstone.lt), [ported/happy_numbers.lt](../conformance/ported/happy_numbers.lt), [ported/josephus.lt](../conformance/ported/josephus.lt), [ported/sieve.lt](../conformance/ported/sieve.lt), [values/passed_in_loops.lt](../conformance/values/passed_in_loops.lt), [values/passed_in_while_head.lt](../conformance/values/passed_in_while_head.lt).

<a id="expressions.for-iterables"></a>
In a `for`, `e` is one of:

- a `List<T>`, which yields values of type `T`;
- a `Map<K, V>`, which yields `(K, V)` pairs in insertion order ([std.maps](17-std.md#std.maps));
- a range of integers ([expressions.range-iteration](#expressions.range-iteration));
- an array ([generics.array-iteration](07-types.md#generics.array-iteration));
- a view or an iterator ([views.for-over-view](13-modes.md#views.for-over-view));
- the fields or the cases of a type ([meta.fields](16-meta.md#meta.fields), [meta.variant-cases](16-meta.md#meta.variant-cases)).

An `e` of any other type is a type mismatch (E0311).

Tests: [expressions/for_iterables.lt](../conformance/expressions/for_iterables.lt), [modes/iterate_non_place.lt](../conformance/modes/iterate_non_place.lt), [modes/modify_while_iterating.lt](../conformance/modes/modify_while_iterating.lt), [patterns/irrefutable_positions.lt](../conformance/patterns/irrefutable_positions.lt), [std/loops_over_pairs.lt](../conformance/std/loops_over_pairs.lt), [std/map_order.lt](../conformance/std/map_order.lt), [std/maps.lt](../conformance/std/maps.lt).

<a id="expressions.range-iteration"></a>
`a..b` yields the integers from `a` up to but excluding `b`, and `a..=b` includes `b`. Both bounds are evaluated once, `a` first, before the first iteration. A range whose bounds aren't integers, as `0.0..1.5`, is E0317, at its start. The bounds' types needn't be known where they stand ([types.range-bounds](07-types.md#types.range-bounds)).

Tests: [expressions/range_bounds_from_loop_variable.lt](../conformance/expressions/range_bounds_from_loop_variable.lt), [expressions/range_ends.lt](../conformance/expressions/range_ends.lt), [expressions/ranges.lt](../conformance/expressions/ranges.lt), [ported/fizzbuzz.lt](../conformance/ported/fizzbuzz.lt), [ported/hundred_doors.lt](../conformance/ported/hundred_doors.lt), [types/range_of_floats.lt](../conformance/types/range_of_floats.lt).

<a id="expressions.break-and-continue"></a>
`break` and `continue` take no labels and no values, so `break 5` is a syntax error (E0100). Each acts on the innermost loop whose body holds it. One outside the body of every loop, or separated from its loop by a closure ([expressions.closure-boundaries](#expressions.closure-boundaries)), is E0216. The head of a `while` and the iterable of a `for` are outside the loop's body.

Tests: [expressions/break_across_closure.lt](../conformance/expressions/break_across_closure.lt), [expressions/break_with_value.lt](../conformance/expressions/break_with_value.lt), [expressions/if_let_loops.lt](../conformance/expressions/if_let_loops.lt), [expressions/jumps_in_heads.lt](../conformance/expressions/jumps_in_heads.lt), [expressions/jumps_outside_loops.lt](../conformance/expressions/jumps_outside_loops.lt), [expressions/range_ends.lt](../conformance/expressions/range_ends.lt), [names/break_outside_loop.lt](../conformance/names/break_outside_loop.lt), [ported/hamming_numbers.lt](../conformance/ported/hamming_numbers.lt).

<a id="expressions.loop-types"></a>
`while` and `for` have type `()`. A `loop` has type `()` when its body contains a `break` that exits it, and type `Never` otherwise.

Tests: [expressions/loop_body_value.lt](../conformance/expressions/loop_body_value.lt), [expressions/loop_never.lt](../conformance/expressions/loop_never.lt), [expressions/loop_value_types.lt](../conformance/expressions/loop_value_types.lt), [types/loop_break_in_with.lt](../conformance/types/loop_break_in_with.lt), [types/loop_types.lt](../conformance/types/loop_types.lt).

## Assignment and places

<a id="expressions.assignment"></a>
An **assignment** is `place = e`, or `place op= e` with one of the compound operators of the `assign_op` production ([syntax.blocks](03-syntax.md#syntax.blocks)). [values.assignment-order](05-values.md#values.assignment-order) and [values.compound-assignment-order](05-values.md#values.compound-assignment-order) give the order in which it evaluates. Assignment is a statement, never an expression, so `if x = y {` is a syntax error (E0100).

Tests: [expressions/assignment_in_condition.lt](../conformance/expressions/assignment_in_condition.lt), [expressions/assignment_not_expression.lt](../conformance/expressions/assignment_not_expression.lt), [expressions/compound_assignment_forms.lt](../conformance/expressions/compound_assignment_forms.lt), [ported/sieve.lt](../conformance/ported/sieve.lt).

<a id="expressions.places"></a>
A place is one of these:

- `x`, `place.f`, `place.0` or `place[i]` ([modes.places](13-modes.md#modes.places));
- `v[i]`, for a binding `v` of a view of a list ([projections.places-through-views](13-modes.md#projections.places-through-views));
- a projection's call ([projections.call-is-place](13-modes.md#projections.call-is-place)).

A field read through an `Option` is not a place, and neither is a field or an element of one ([types.option-field-not-place](07-types.md#types.option-field-not-place)). Where a place is required, as the target of an assignment or an `inout` argument, anything else is E0401, *not a place*.

Tests: [checking/assignment_to_unknown_name.lt](../conformance/checking/assignment_to_unknown_name.lt), [expressions/fields_through_options_nested_place.lt](../conformance/expressions/fields_through_options_nested_place.lt), [expressions/fields_through_options_not_a_place.lt](../conformance/expressions/fields_through_options_not_a_place.lt), [expressions/fields_through_options_places.lt](../conformance/expressions/fields_through_options_places.lt), [expressions/not_a_place.lt](../conformance/expressions/not_a_place.lt), [modes/inout_marks_in_phase_one.lt](../conformance/modes/inout_marks_in_phase_one.lt), [modes/places.lt](../conformance/modes/places.lt).

<a id="expressions.mutable-places"></a>
The place of an assignment must be rooted in a `var` binding or an `inout` parameter of the body ([modes.what-can-be-modified](13-modes.md#modes.what-can-be-modified)). Any other place there is E0403, *modifying what can't be modified*.

Tests: [modes/read_only_bindings.lt](../conformance/modes/read_only_bindings.lt), [values/let_immutable.lt](../conformance/values/let_immutable.lt), [values/strings_immutable.lt](../conformance/values/strings_immutable.lt), [values/var_parts.lt](../conformance/values/var_parts.lt).

## Conditions

<a id="expressions.conditions"></a>
Each of these must have type `bool` (E0311):

- the condition of an `if` or a `while`;
- the guard of a `match` or `catch` arm;
- the operand of `assert` ([program.assert-expr](04-programs.md#program.assert-expr));
- both operands of `&&` and `||`.

`a && b` evaluates `b` only when `a` is `true`, and `a || b` evaluates `b` only when `a` is `false`.

Tests: [expressions/conditions_are_bool.lt](../conformance/expressions/conditions_are_bool.lt), [expressions/logical_short_circuit.lt](../conformance/expressions/logical_short_circuit.lt), [types/logical_operand_not_bool.lt](../conformance/types/logical_operand_not_bool.lt).

## Scope

<a id="expressions.scope"></a>
A name bound in a body is visible from where its binding takes effect to the end of the construct that holds it:

- a `let` or `var` statement, from the next statement to the end of its block, so `let x = x + 1` reads the `x` bound before it;
- the bindings of a let-else, likewise from after its statement ([patterns.let-else](09-patterns.md#patterns.let-else));
- a parameter, in the whole body of its function or closure;
- the pattern of a `for` head, in the loop's body;
- the pattern of a `match` or `catch` arm, in its guard and its body;
- the pattern of an `if let`, in its first block ([expressions.if-let](#expressions.if-let)).

A name used where no binding or item of that name is visible is E0211, *unknown name*.

Tests: [expressions/if_let_scope.lt](../conformance/expressions/if_let_scope.lt), [expressions/scope_and_shadowing.lt](../conformance/expressions/scope_and_shadowing.lt), [expressions/scope_ends.lt](../conformance/expressions/scope_ends.lt).

<a id="expressions.shadowing"></a>
A binding may reuse the name of a visible binding, which it hides until its own scope ends. It may also reuse the name of an item, a prelude item included, which it hides in the same way. Two kinds of name are exceptions: the names that `use` declarations bind (E0207, [program.one-value-namespace](04-programs.md#program.one-value-namespace)), and value parameters ([generics.value-parameters-in-body](07-types.md#generics.value-parameters-in-body)).

Tests: [expressions/scope_and_shadowing.lt](../conformance/expressions/scope_and_shadowing.lt).
