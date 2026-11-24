# 12. Effects and handlers

A function's row says what the function does besides compute its result: whether it reaches the world, which error it can raise, and which user-defined effects it performs. This chapter gives rows, how a body's effects are inferred, and the parameters whose effects pass through to the caller. It then gives raising and handling errors with `raise`, `try` and `catch`, failure kept as data, and panics and the `without panic` limit. Last come the effects and handlers of the advanced tier. [Types](07-types.md) defines expected types, [Patterns](09-patterns.md) the arms of a `catch`, and [Inferred facts](15-facts.md) the implicit effects `panic` and `alloc`.

## Rows

<a id="effects.rows"></a>
A function's **row** is written `/ x` or `/ {x, …}` after its return type, or after its parameter list when it has no return type (the `row` production, [syntax.rows](03-syntax.md#syntax.rows)). Each element of a row is one of these:

- the label `io`, a contextual keyword ([lexical.contextual-keywords](02-lexical.md#lexical.contextual-keywords));
- a label `raise<E>`;
- an effect ([handlers.effects-in-rows](#handlers.effects-in-rows));
- a **row variable**: any other lowercase identifier, declared in the function's generic list, as in `fn compose<A, B, C, e>(…)`.

Elements are unordered, so `/ {io, raise<str>}` and `/ {raise<str>, io}` are one row. A function with no row has no explicit effects.

Tests: [effects/catch_row_variables.lt](../conformance/effects/catch_row_variables.lt), [effects/effects_fit_row.lt](../conformance/effects/effects_fit_row.lt), [effects/row_elements.lt](../conformance/effects/row_elements.lt), [effects/rows.lt](../conformance/effects/rows.lt).

<a id="effects.row-variables"></a>
Only functions declare row variables. A lowercase generic of a type or an `impl` block is a syntax error (E0100). A function writes its row variables in its own row, in its result type, and in the types of its parameters that aren't non-escaping ([effects.non-escaping-parameters](#effects.non-escaping-parameters)). A row variable written in the type of a non-escaping parameter, at any depth, is E0509, *row variable on a parameter that passes its effects through*. It is reported at the first row variable written in that type, once for each such parameter, and the parameter's type is then the error type. A lowercase name in a row that the function doesn't declare is an unknown name (E0211).

Tests: [declarations/row_variable_on_impl.lt](../conformance/declarations/row_variable_on_impl.lt), [declarations/row_variable_on_type.lt](../conformance/declarations/row_variable_on_type.lt), [effects/row_variable_on_parameter.lt](../conformance/effects/row_variable_on_parameter.lt), [names/unknown_names.lt](../conformance/names/unknown_names.lt).

<a id="effects.repeated-elements"></a>
A row holds `io` at most once and at most one `raise<E>` label, and a written row holds at most one row variable. A second `io`, a second `raise` label and a second row variable are each E0500, *repeated row element*, at the repeated element. A row holds each effect once too ([handlers.effects-in-rows](#handlers.effects-in-rows)). The implicit row variables of non-escaping parameters are never written, so a function's own row, and the rows that a body forms, may hold several of them.

Tests: [effects/row_elements.lt](../conformance/effects/row_elements.lt), [names/row_elements.lt](../conformance/names/row_elements.lt).

<a id="effects.effect-names"></a>
A row variable can't be named `io`, which in a row is always the label. Nor can it be named `panic` or `alloc`, which are implicit effects and never written ([facts.implicit-effects](15-facts.md#facts.implicit-effects)). Each of these names is E0501, *effect name as a row variable*, where the variable is declared or written. `panic` or `alloc` written as an element of a row is E0501 too.

Tests: [effects/row_elements.lt](../conformance/effects/row_elements.lt), [implicit/rows.lt](../conformance/implicit/rows.lt), [names/row_elements.lt](../conformance/names/row_elements.lt).

<a id="effects.other-effects"></a>
`panic` and `alloc` are implicit: the compiler infers them from bodies, and no row writes them ([facts.implicit-effects](15-facts.md#facts.implicit-effects)). `async` ([tasks.async](14-tasks.md#tasks.async)) and user-defined effects ([handlers.declaring-effect](#handlers.declaring-effect)) belong to the advanced tier.

Tests: [effects/implicit_effects.lt](../conformance/effects/implicit_effects.lt), [tasks/async_in_core.lt](../conformance/tasks/async_in_core.lt).

## Inference

<a id="effects.inference"></a>
A body's effects are inferred, and they must fit within its declared row. A call contributes its callee's row as instantiated at the call. That row holds what the arguments given to the callee's non-escaping parameters pass through ([effects.non-escaping-parameters](#effects.non-escaping-parameters)). A closure literal contributes nothing where it is written. Its body's effects become part of the closure's type, and fit the closure's own row, apart from the row of the body around it. An effect that doesn't fit a row is E0502, *effect that doesn't fit the row*, at the first call, `raise` or performance in the body that performs it.

Tests: [declarations/function_type_rows.lt](../conformance/declarations/function_type_rows.lt), [effects/closure_rows.lt](../conformance/effects/closure_rows.lt), [effects/declared_error_type.lt](../conformance/effects/declared_error_type.lt), [effects/effects_fit_row.lt](../conformance/effects/effects_fit_row.lt), [effects/escaping_exact_row_rejected.lt](../conformance/effects/escaping_exact_row_rejected.lt), [effects/later_effects.lt](../conformance/effects/later_effects.lt), [effects/pass_through.lt](../conformance/effects/pass_through.lt), [effects/raise_from_arm.lt](../conformance/effects/raise_from_arm.lt), [effects/raise_kept_past_a_refused_effect.lt](../conformance/effects/raise_kept_past_a_refused_effect.lt), [effects/rows.lt](../conformance/effects/rows.lt), [procedural/reaching_io/main.lt](../conformance/procedural/reaching_io/main.lt).

<a id="effects.missing-effects"></a>
A row that a body's effects don't fit gets one E0502 for each of these, at the first call, `raise` or performance that performs it:

- `io`;
- raising, whatever the error types;
- each effect;
- each row variable.

Later ones that don't fit the same row aren't reported. So `fn f() { raise "y"; raise 1 }` gets one E0502, at the first `raise`. A closure in that body whose own row lacks an effect gets an E0502 of its own.

Tests: [effects/closure_rows.lt](../conformance/effects/closure_rows.lt), [effects/effects_fit_row.lt](../conformance/effects/effects_fit_row.lt), [effects/missing_effects.lt](../conformance/effects/missing_effects.lt), [effects/missing_effects_per_label.lt](../conformance/effects/missing_effects_per_label.lt), [effects/two_raises_without_row.lt](../conformance/effects/two_raises_without_row.lt).

<a id="effects.one-error-type"></a>
A body raises at most one error type. A body that raises a type other than the one its row declares is E0503, *two error types*, at the first `raise` or call that does. A closure's body and the operand of a `try … catch` declare no row. In them, the first `raise` or raising call in evaluation order fixes the error type. A later one that raises another type is E0503. A row gets one E0503, at the first `raise` or call that raises a second error type.

Tests: [effects/closure_arguments_meet.lt](../conformance/effects/closure_arguments_meet.lt), [effects/declared_error_type.lt](../conformance/effects/declared_error_type.lt), [effects/paired_given_its_type.lt](../conformance/effects/paired_given_its_type.lt), [effects/paired_own_row_given_other_raise.lt](../conformance/effects/paired_own_row_given_other_raise.lt), [effects/raise_and_catch.lt](../conformance/effects/raise_and_catch.lt), [effects/raise_kept_past_a_refused_effect.lt](../conformance/effects/raise_kept_past_a_refused_effect.lt), [effects/three_raises_in_closure.lt](../conformance/effects/three_raises_in_closure.lt), [effects/two_error_types.lt](../conformance/effects/two_error_types.lt), [effects/two_error_types_without_row.lt](../conformance/effects/two_error_types_without_row.lt), [effects/two_raises_without_row.lt](../conformance/effects/two_raises_without_row.lt).

<a id="effects.rows-that-meet"></a>
Two function types must sometimes be one, as for branches, list elements, arms, or two arguments of one type parameter's type. If their rows together would hold two `raise` labels, the error is at the first expression that brings the second error type:

- A function value whose type is already formed, as a variable's is, is a type mismatch there (E0311, [types.mismatch](07-types.md#types.mismatch)).
- A closure literal is checked against the type the earlier ones set ([types.expected-types](07-types.md#types.expected-types)), so its body raises into their common row. The `raise` or call in it that raises the second type is E0503.

So `if c { f } else { g }`, with `f` raising `A` and `g` raising `B`, is E0311 at `g`. `if c { || raise A1 } else { || raise B1 }` is E0503 at `raise B1`. For `fn pick<T>(x: T, y: T) -> T`, `pick(f, g)` is E0311 at `g`.

Tests: [effects/branch_values_raising_different_types.lt](../conformance/effects/branch_values_raising_different_types.lt), [effects/branches_raising_different_types.lt](../conformance/effects/branches_raising_different_types.lt), [effects/closure_arguments_meet.lt](../conformance/effects/closure_arguments_meet.lt), [effects/function_arguments_meet.lt](../conformance/effects/function_arguments_meet.lt), [effects/paired_given_function_value.lt](../conformance/effects/paired_given_function_value.lt).

## Function values

<a id="effects.function-values"></a>
A function value fits where a function type with a larger row is expected, so a pure function fits `fn(A) -> B / io`. The row may grow only where a function value is checked against an expected type ([types.expected-types](07-types.md#types.expected-types)). Those places are an argument, an annotated value, an assigned or returned value, a field or element of a literal, and a branch or element after the first. A function type inside another type must match exactly, so a `List<fn()>` is not a `List<fn() / io>` (E0311).

Tests: [effects/escaping_exact_row.lt](../conformance/effects/escaping_exact_row.lt), [effects/function_arguments_meet.lt](../conformance/effects/function_arguments_meet.lt), [effects/function_value_rows.lt](../conformance/effects/function_value_rows.lt), [effects/paired_with_another_type.lt](../conformance/effects/paired_with_another_type.lt), [effects/pure_list_variable.lt](../conformance/effects/pure_list_variable.lt), [effects/unpaired_annotated_row.lt](../conformance/effects/unpaired_annotated_row.lt), [traits/tuple_elements.lt](../conformance/traits/tuple_elements.lt).

<a id="effects.function-value-unions"></a>
Where branches, or the elements of a list literal, are function values, their common type has the union of their rows, whatever their order. So `if c { quiet } else { loud }` and `[quiet, loud]` both have type `fn() / io` when `loud` performs `io`.

Tests: [effects/branch_values_raising_different_types.lt](../conformance/effects/branch_values_raising_different_types.lt), [effects/branches_raising_different_types.lt](../conformance/effects/branches_raising_different_types.lt), [effects/function_value_orders.lt](../conformance/effects/function_value_orders.lt).

<a id="effects.inout-function-arguments"></a>
An `inout` argument's type must be its parameter's exactly, row included (E0311).

Tests: [effects/inout_function_parameter.lt](../conformance/effects/inout_function_parameter.lt), [effects/inout_rows.lt](../conformance/effects/inout_rows.lt).

## Parameters that pass effects through

<a id="effects.non-escaping-parameters"></a>
A parameter of a declared function or method whose type is a function type is **non-escaping**, unless it is `inout` or written `escaping` ([declarations.function-declarations](10-declarations.md#declarations.function-declarations)). Its type `fn(A) -> B / R` stands for `fn(A) -> B / {R, ρ}`. Here `ρ` is an implicit row variable of its own, which no program writes, and the function's own row holds every such `ρ`. Each use of the function instantiates `ρ` as it does a written row variable, with what the argument's row holds beyond `R`. So `R` lists the argument's effects that the function takes charge of. The argument's other effects **pass through**: the call performs them in the caller, and the caller's `try` marks a raise among them ([effects.marking](#effects.marking)). A raise that passes through belongs to the caller, so a `catch` in the function handles it only when `R` names its type ([effects.catch-around-row-variables](#effects.catch-around-row-variables)).

Tests: [declarations/function_limits.lt](../conformance/declarations/function_limits.lt), [declarations/functions.lt](../conformance/declarations/functions.lt), [effects/effects_fit_row.lt](../conformance/effects/effects_fit_row.lt), [effects/handled_by_parameter_row.lt](../conformance/effects/handled_by_parameter_row.lt), [effects/inout_function_parameter.lt](../conformance/effects/inout_function_parameter.lt), [effects/pass_through.lt](../conformance/effects/pass_through.lt), [effects/pass_through_marked.lt](../conformance/effects/pass_through_marked.lt), [effects/row_variable_on_parameter.lt](../conformance/effects/row_variable_on_parameter.lt), [effects/rows.lt](../conformance/effects/rows.lt), [implicit/without_alloc/main.lt](../conformance/implicit/without_alloc/main.lt), [traits/non_escaping_method.lt](../conformance/traits/non_escaping_method.lt).

<a id="effects.no-escape"></a>
Each occurrence of a non-escaping parameter in its function's body must be one of these, and so must each closure literal that contains one at any depth:

- the callee of a call;
- an argument given to a non-escaping parameter of the function or method that a call names.

Anything else is E0508, *function parameter that escapes*. These uses of the parameter are E0508:

- storing it in a record, a variant, a list, a map or a tuple;
- returning it;
- binding it to a local;
- assigning it;
- passing it to any other parameter, a function value's included.

The error offers a fix that writes `escaping` before the parameter. Each parameter that escapes gets one E0508, at the first occurrence or closure literal in source order that breaks the rule. A row that doesn't hold a parameter's implicit row variable, where the variable meets it, is no error of its own. The variable reaches such a row only through a use that breaks this rule.

Tests: [effects/closure_passed_on.lt](../conformance/effects/closure_passed_on.lt), [effects/escapes.lt](../conformance/effects/escapes.lt).

<a id="effects.escaping-parameters"></a>
An `escaping` parameter's row is exactly the row its type writes. A function that keeps an argument and stays generic in its effects writes a row variable in that row, paired as [effects.paired-row-variables](#effects.paired-row-variables) gives. `compose` does this: `fn compose<A, B, C, e>(escaping f: fn(A) -> B / e, escaping g: fn(B) -> C / e) -> fn(A) -> C / e`.

Tests: [effects/escaping_exact_row.lt](../conformance/effects/escaping_exact_row.lt), [effects/escaping_exact_row_rejected.lt](../conformance/effects/escaping_exact_row_rejected.lt), [effects/escaping_paired.lt](../conformance/effects/escaping_paired.lt), [effects/raise_kept_past_a_refused_effect.lt](../conformance/effects/raise_kept_past_a_refused_effect.lt), [effects/row_elements.lt](../conformance/effects/row_elements.lt), [expressions/trailing_commas.lt](../conformance/expressions/trailing_commas.lt), [traits/escaping_mismatch.lt](../conformance/traits/escaping_mismatch.lt).

<a id="effects.closure-parameters"></a>
A closure literal's parameters are never non-escaping. Their types, rows included, are inferred from how the enclosing body uses the closure, or written in an annotation ([expressions.closure-parameter-types](08-expressions.md#expressions.closure-parameter-types)). So in a pure function, `let call = |g| g()` followed by `call(|| print("x"))` is E0502 at the call. The closure's `io` reaches the body through `call`.

Tests: [effects/closure_rows.lt](../conformance/effects/closure_rows.lt), [effects/later_effects.lt](../conformance/effects/later_effects.lt).

## Raising and marking

<a id="effects.raise"></a>
`raise e` has type `Never` and performs `raise<E>`, where `E` is the type of `e`. It needs no `try`.

Tests: [effects/effects_fit_row.lt](../conformance/effects/effects_fit_row.lt), [effects/missing_effects.lt](../conformance/effects/missing_effects.lt), [effects/raise_and_catch.lt](../conformance/effects/raise_and_catch.lt), [ported/roman_numerals.lt](../conformance/ported/roman_numerals.lt).

<a id="effects.error-type-raises"></a>
A raise of the error type fits every row, needs no `try`, and is handled by every `catch`. A call to a function whose row is `raise<ParseEror>` raises the error type when `ParseEror` names no type (E0211). Such a raise causes no diagnostic ([errors.error-type](18-errors.md#errors.error-type)).

Tests: [effects/raise_of_error_type.lt](../conformance/effects/raise_of_error_type.lt).

<a id="effects.marking"></a>
`try e` has the type and the effects of `e`, and changes nothing else: it marks the calls in `e` that can raise. Every call whose callee's row, as instantiated at the call, holds a `raise` label must sit inside the operand of some `try`. The `try` may be outside the closure literal that holds the call, so `try xs.map(|l| parse(l))` marks both `map` and `parse`. The arms of a `catch` are not part of its operand, so a raising call inside an arm needs a `try` of its own. A raising call with no `try` is E0505, *raising call without `try`*, which offers a fix that inserts one.

Tests: [checking/error_type_in_try_and_match.lt](../conformance/checking/error_type_in_try_and_match.lt), [checking/phases.lt](../conformance/checking/phases.lt), [effects/marking.lt](../conformance/effects/marking.lt), [effects/pass_through.lt](../conformance/effects/pass_through.lt), [effects/pass_through_marked.lt](../conformance/effects/pass_through_marked.lt), [effects/phase_interplay.lt](../conformance/effects/phase_interplay.lt), [effects/raise_and_catch.lt](../conformance/effects/raise_and_catch.lt), [effects/raising_closure_called_later.lt](../conformance/effects/raising_closure_called_later.lt), [ported/roman_numerals.lt](../conformance/ported/roman_numerals.lt).

<a id="effects.empty-try"></a>
A `try` without `catch` whose operand contains no raising call is W0500, *`try` with nothing to mark*. So is a `try … catch` whose operand raises nothing, so that its error type is `Never` ([effects.catch](#effects.catch)). The arms of such a `catch` never run, and get neither W0301 ([patterns.unreachable-arms](09-patterns.md#patterns.unreachable-arms)) nor W0501 ([effects.catch-alls-need-reason](#effects.catch-alls-need-reason)).

Tests: [effects/empty_try.lt](../conformance/effects/empty_try.lt), [effects/empty_try_arms.lt](../conformance/effects/empty_try_arms.lt), [effects/results.lt](../conformance/effects/results.lt).

## Handling errors

<a id="effects.catch-syntax"></a>
`try e catch P => x` has a single arm. `try e catch { arms }` takes arms with the syntax of `match` arms, guards included, separated by terminators or commas (the `catch_arm` production, [syntax.expressions](03-syntax.md#syntax.expressions)). A `catch` belongs to the innermost `try` whose operand is still open where the `catch` appears ([syntax.catch-attachment](03-syntax.md#syntax.catch-attachment)).

Tests: [effects/because_on_arm.lt](../conformance/effects/because_on_arm.lt), [effects/catch_all_forms.lt](../conformance/effects/catch_all_forms.lt), [effects/catch_all_uses_error.lt](../conformance/effects/catch_all_uses_error.lt), [effects/catch_alls.lt](../conformance/effects/catch_alls.lt), [effects/guard_with_reason.lt](../conformance/effects/guard_with_reason.lt), [expressions/catch_binding.lt](../conformance/expressions/catch_binding.lt), [expressions/head_catch_block.lt](../conformance/expressions/head_catch_block.lt), [expressions/parenthesized_heads.lt](../conformance/expressions/parenthesized_heads.lt).

<a id="effects.catch"></a>
The error type `E` of `try e catch arms` is the type that `e` raises, and `Never` when `e` raises nothing. That type includes raises through a function value that `e` calls, even one whose row is known only later. The expression's effects are those of `e` without `raise<E>`, together with those of the arms. Its type is the common type of `e` and the arms. The arms must cover `E` exhaustively, or the `try` is E0329, *patterns that don't cover every value* ([patterns.non-exhaustive-matches](09-patterns.md#patterns.non-exhaustive-matches)). So `catch {}` handles only `Never`. An arm may raise again, with the same or another error type, and that raise goes to the enclosing context.

Tests: [checking/error_type_in_try_and_match.lt](../conformance/checking/error_type_in_try_and_match.lt), [effects/catch_alls.lt](../conformance/effects/catch_alls.lt), [effects/catch_covers_error.lt](../conformance/effects/catch_covers_error.lt), [effects/empty_catch.lt](../conformance/effects/empty_catch.lt), [effects/empty_try_arms.lt](../conformance/effects/empty_try_arms.lt), [effects/phase_interplay.lt](../conformance/effects/phase_interplay.lt), [effects/raise_and_catch.lt](../conformance/effects/raise_and_catch.lt), [effects/raise_from_arm.lt](../conformance/effects/raise_from_arm.lt), [ported/roman_numerals.lt](../conformance/ported/roman_numerals.lt), [std/io_errors/main.lt](../conformance/std/io_errors/main.lt).

<a id="effects.innermost-catch"></a>
At run time, a raise transfers control to the innermost `try … catch` whose operand is still being evaluated. This holds for a raise inside a closure that the operand calls too. A closure carries its raise in its type, so a closure that leaves the operand, as by being returned, needs a `try` again wherever it is called. Each `inout` argument of the calls that the raise ends holds what the callee wrote before the raise ([values.inout-arguments](05-values.md#values.inout-arguments)).

Tests: [effects/raise_and_catch.lt](../conformance/effects/raise_and_catch.lt), [effects/raising_closure_called_later.lt](../conformance/effects/raising_closure_called_later.lt), [expressions/catch_binding.lt](../conformance/expressions/catch_binding.lt), [expressions/closure_inout_raise.lt](../conformance/expressions/closure_inout_raise.lt), [values/inout_on_raise.lt](../conformance/values/inout_on_raise.lt), [values/inout_raise_through_calls.lt](../conformance/values/inout_raise_through_calls.lt), [values/passed_on_raise_paths.lt](../conformance/values/passed_on_raise_paths.lt).

<a id="effects.catch-alls-need-reason"></a>
An arm without a guard whose pattern is `_` or a variable is a **catch-all**. A catch-all needs nothing more in either of these cases:

- it raises: its body is a `raise`, or a block whose final expression is one;
- its pattern is a variable that its body uses, inside a closure or an interpolation too, but not through a later binding that shadows it.

So `catch e => return Err(Bad(e))` needs no reason. Any other catch-all gives a reason, with `because` and a string literal between its pattern and `=>`, in either form of `catch`. An example is `catch _ because "old configs omit the port" => 8080`. A catch-all with neither a raise, a use of its error nor a reason is W0501, *catch-all without a reason*. A catch-all that can never match gets only W0301 instead ([patterns.unreachable-arms](09-patterns.md#patterns.unreachable-arms)).

Tests: [checking/error_type_in_try_and_match.lt](../conformance/checking/error_type_in_try_and_match.lt), [effects/catch_all_forms.lt](../conformance/effects/catch_all_forms.lt), [effects/catch_all_uses_error.lt](../conformance/effects/catch_all_uses_error.lt), [effects/catch_alls.lt](../conformance/effects/catch_alls.lt), [effects/phase_interplay.lt](../conformance/effects/phase_interplay.lt).

<a id="effects.reasons-only-on-catch-alls"></a>
`because` on an arm that isn't a catch-all is E0504, *reason on an arm that isn't a catch-all*, even when the arm names the only variant of the error type. An arm with a guard can't take `because` at all, and the reason is a string literal with no interpolation. The grammar rejects both (E0100).

Tests: [effects/because_on_arm.lt](../conformance/effects/because_on_arm.lt), [effects/guard_with_reason.lt](../conformance/effects/guard_with_reason.lt), [effects/interpolated_reason.lt](../conformance/effects/interpolated_reason.lt), [effects/single_variant_errors.lt](../conformance/effects/single_variant_errors.lt).

## Failures that pass through

<a id="effects.paired-row-variables"></a>
A function's signature **pairs** a row variable `v`, written or implicit, with an error type `E` when some row of the signature holds both `v` and `raise<E>`. The rows of a signature are the row of each parameter's type, at any depth, and the function's own row. A non-escaping parameter's implicit variable is in that parameter's row and in the function's own row. So the signature pairs it with `E` when either row names `raise<E>`, as `fn or_zero<E>(f: fn() -> i64 / raise<E>) -> i64` does. A signature pairs a row variable with an effect in the same way ([handlers.with-pairing](#handlers.with-pairing)).

Tests: [effects/escaping_paired.lt](../conformance/effects/escaping_paired.lt), [effects/handled_by_parameter_row.lt](../conformance/effects/handled_by_parameter_row.lt), [effects/paired_in_nested_parameter.lt](../conformance/effects/paired_in_nested_parameter.lt), [effects/paired_rows.lt](../conformance/effects/paired_rows.lt), [effects/paired_with_another_type.lt](../conformance/effects/paired_with_another_type.lt).

<a id="effects.catch-around-row-variables"></a>
Take a call in the operand of a `catch` whose callee's row, as instantiated at the call, holds a row variable `v` of the enclosing function, written or implicit. The call is E0506, *`catch` around a failure that belongs to the caller*, at the call, unless that row also holds `raise<E>` and the enclosing signature pairs `v` with `E`. A call through a row that holds several such variables gets one E0506.

The rule skips a call inside a closure literal that is itself inside the operand. It also skips a call inside the operand of a nearer `catch` inside it, which that `catch` reports. A `catch` that sits inside a closure literal is checked like any other, its operand being the code between `try` and `catch`. Tests and doc examples have no parameters and declare no row variables, so the rule never applies to their bodies.

Tests: [effects/catch_inside_closure_unpaired.lt](../conformance/effects/catch_inside_closure_unpaired.lt), [effects/catch_row_variables.lt](../conformance/effects/catch_row_variables.lt), [effects/closure_in_catch_operand.lt](../conformance/effects/closure_in_catch_operand.lt), [effects/escaping_paired.lt](../conformance/effects/escaping_paired.lt), [effects/handled_by_parameter_row.lt](../conformance/effects/handled_by_parameter_row.lt), [effects/nested_catch_row_variable.lt](../conformance/effects/nested_catch_row_variable.lt), [effects/paired_in_nested_parameter.lt](../conformance/effects/paired_in_nested_parameter.lt), [effects/paired_rows.lt](../conformance/effects/paired_rows.lt), [effects/paired_with_another_type.lt](../conformance/effects/paired_with_another_type.lt), [effects/passed_reported_once_in_catch.lt](../conformance/effects/passed_reported_once_in_catch.lt), [effects/passed_to_paired_parameter_paired.lt](../conformance/effects/passed_to_paired_parameter_paired.lt), [effects/unpaired_annotated_row.lt](../conformance/effects/unpaired_annotated_row.lt), [effects/unpaired_instantiated_row.lt](../conformance/effects/unpaired_instantiated_row.lt).

<a id="effects.passing-to-paired-variables"></a>
A use of a function, called or taken as a value, instantiates the row variables of its signature, written and implicit. Suppose the signature pairs a row variable `v` with an error type `E`. Suppose too that the use gives `v` a row that holds a row variable `r` of the enclosing function, written or implicit. Then the enclosing signature must pair `r` with the type that the use gives `E`. Otherwise the use is E0507, *failures passed on without their error type*, at the use. The rule applies inside closure literals too. So `fn wrap(g: fn() -> i64) -> Result<i64, Box> { Result.of(g) }` is E0507, and with `g: fn() -> i64 / raise<Box>` it is accepted.

Tests: [effects/passed_as_value_unpaired.lt](../conformance/effects/passed_as_value_unpaired.lt), [effects/passed_concrete_row.lt](../conformance/effects/passed_concrete_row.lt), [effects/passed_in_closure_unpaired.lt](../conformance/effects/passed_in_closure_unpaired.lt), [effects/passed_paired_with_another_type.lt](../conformance/effects/passed_paired_with_another_type.lt), [effects/passed_to_paired_parameter_paired.lt](../conformance/effects/passed_to_paired_parameter_paired.lt), [effects/passed_to_paired_parameter_unpaired.lt](../conformance/effects/passed_to_paired_parameter_unpaired.lt), [effects/passed_to_result_of_paired.lt](../conformance/effects/passed_to_result_of_paired.lt), [effects/passed_to_result_of_unpaired.lt](../conformance/effects/passed_to_result_of_unpaired.lt).

<a id="effects.passing-reports"></a>
A use gets one E0507 for each variable of the callee's signature that it gives a row holding an unpaired row variable. This holds however many rows of the signature pair that variable, and however many unpaired variables the row holds. So a use that gives `r` to two variables, one paired with `Box` and one with `Tag`, gets two. A call that E0506 already reports, because a `catch` surrounds it, gets no E0507.

Tests: [effects/passed_paired_twice.lt](../conformance/effects/passed_paired_twice.lt), [effects/passed_reported_once_in_catch.lt](../conformance/effects/passed_reported_once_in_catch.lt), [effects/passed_to_two_paired_variables.lt](../conformance/effects/passed_to_two_paired_variables.lt).

<a id="effects.what-paired-variable-may-raise"></a>
When a use gives a paired variable `v` a row that raises `F`, `F` must be the type that the use gives `E`. This holds even when no argument's type holds a row with two `raise` labels: the callee's rows that pair `v` would hold two once instantiated. The error is where the second error type comes, as where rows meet ([effects.rows-that-meet](#effects.rows-that-meet)):

- a function value whose type is already formed is E0311;
- the `raise` or call in a closure literal that raises `F` is E0503.

Take `fn f(g: fn() -> i64) -> i64 / raise<str>`, whose own row pairs the implicit variable of `g` with `str`. The call `f(|| raise true)` is E0503 at `raise true`.

Tests: [effects/paired_given_function_value.lt](../conformance/effects/paired_given_function_value.lt), [effects/paired_given_its_type.lt](../conformance/effects/paired_given_its_type.lt), [effects/paired_only_in_empty_list.lt](../conformance/effects/paired_only_in_empty_list.lt), [effects/paired_own_row_given_other_raise.lt](../conformance/effects/paired_own_row_given_other_raise.lt), [effects/paired_parameter_row_given_other_raise.lt](../conformance/effects/paired_parameter_row_given_other_raise.lt).

## Failure as data

<a id="effects.result"></a>
`Result<T, E>` stores failure as data ([std.option-result-and-ordering](17-std.md#std.option-result-and-ordering)). `try` acts only on the `raise` effect and never unwraps a `Result`. So `try r` on a `Result` marks nothing (W0500) and is still a `Result`. The conversions are explicit: `r.get()` raises the `E` of an `Err`, and `Result.of(|| e)` captures a raise of `e` as an `Err`.

Tests: [effects/empty_try.lt](../conformance/effects/empty_try.lt), [effects/results.lt](../conformance/effects/results.lt), [effects/try_result.lt](../conformance/effects/try_result.lt), [ported/roman_numerals.lt](../conformance/ported/roman_numerals.lt), [std/option_and_result.lt](../conformance/std/option_and_result.lt), [std/result_get_escapes_main.lt](../conformance/std/result_get_escapes_main.lt).

## Panics

<a id="effects.panic-kinds"></a>
A panic ends the program ([program.exit-statuses](04-programs.md#program.exit-statuses)), and no construct catches it. Every panic has a kind:

| Kind | Raised by | Counts against `without panic` |
| --- | --- | --- |
| `bounds` | An index or range out of bounds, in a list or a string ([std.lists](17-std.md#std.lists), [std.str](17-std.md#std.str)) | Yes |
| `missing-key` | Indexing a map without a default with a missing key ([std.maps](17-std.md#std.maps)) | Yes |
| `divide-by-zero` | Integer division or remainder by zero ([numbers.integer-panics](06-numbers.md#numbers.integer-panics)) | Yes |
| `unreachable` | `unreachable()` ([program.prelude-functions](04-programs.md#program.prelude-functions)) | Yes |
| `assert` | A failed `assert` ([program.assert-expr](04-programs.md#program.assert-expr)) | Yes |
| `explicit` | `panic(msg)` | Yes |
| `hole` | Reaching a typed hole `?` ([declarations.typed-holes](10-declarations.md#declarations.typed-holes)) | Yes |
| `utf8-boundary` | Slicing a string in the middle of a UTF-8 sequence | Yes |
| `unwrap` | `unwrap` or `expect` on a `None` or an `Err` ([std.option-result-and-ordering](17-std.md#std.option-result-and-ordering)) | Yes |
| `nul-in-string` | Lending C a `str` that holds a NUL, with `with_c_str` ([c.lending-buffer](20-builds.md#c.lending-buffer)) | Yes |
| `overflow` | Integer overflow, `MIN / -1`, an invalid shift amount ([numbers.integer-panics](06-numbers.md#numbers.integer-panics)) | No: `without overflow` rules it out ([effects.without-overflow](#effects.without-overflow)) |
| `deadlock` | A `when` on a value that a `when` whose block hasn't ended holds, or one that runs while a `Lazy` computes its value ([shared.when-on-value-already-held](14-tasks.md#shared.when-on-value-already-held)) | No: `without locks` rules it out ([shared.locks](14-tasks.md#shared.locks)) |
| `check-error` | Reaching code with an error, in a program that `run` runs despite its errors ([program.programs-with-errors](04-programs.md#program.programs-with-errors)) | Not applicable: the program doesn't check |

Tests: [declarations/hole_reached.lt](../conformance/declarations/hole_reached.lt), [effects/implicit_effects.lt](../conformance/effects/implicit_effects.lt), [effects/panic_assert.lt](../conformance/effects/panic_assert.lt), [effects/panic_bounds.lt](../conformance/effects/panic_bounds.lt), [effects/panic_divide_by_zero.lt](../conformance/effects/panic_divide_by_zero.lt), [effects/panic_expect.lt](../conformance/effects/panic_expect.lt), [effects/panic_expect_err.lt](../conformance/effects/panic_expect_err.lt), [effects/panic_explicit.lt](../conformance/effects/panic_explicit.lt), [effects/panic_hole.lt](../conformance/effects/panic_hole.lt), [effects/panic_missing_key.lt](../conformance/effects/panic_missing_key.lt), [effects/panic_overflow.lt](../conformance/effects/panic_overflow.lt), [effects/panic_unreachable.lt](../conformance/effects/panic_unreachable.lt), [effects/panic_unwrap.lt](../conformance/effects/panic_unwrap.lt), [effects/panic_unwrap_err.lt](../conformance/effects/panic_unwrap_err.lt), [effects/panic_utf8_boundary.lt](../conformance/effects/panic_utf8_boundary.lt), [effects/without_overflow.lt](../conformance/effects/without_overflow.lt), [effects/without_overflow_runs.lt](../conformance/effects/without_overflow_runs.lt), [effects/without_panic_accepted.lt](../conformance/effects/without_panic_accepted.lt), [effects/without_panic_operations.lt](../conformance/effects/without_panic_operations.lt), [effects/without_panic_unwrap.lt](../conformance/effects/without_panic_unwrap.lt), [handlers/body_panics_after_printing.lt](../conformance/handlers/body_panics_after_printing.lt), [numerics/divide_by_literal_zero.lt](../conformance/numerics/divide_by_literal_zero.lt), [numerics/divide_by_zero.lt](../conformance/numerics/divide_by_zero.lt), [numerics/min_divided_by_minus_one.lt](../conformance/numerics/min_divided_by_minus_one.lt), [numerics/min_remainder_minus_one.lt](../conformance/numerics/min_remainder_minus_one.lt), [numerics/multiplication_overflow.lt](../conformance/numerics/multiplication_overflow.lt), [numerics/negating_the_minimum.lt](../conformance/numerics/negating_the_minimum.lt), [numerics/negative_shift.lt](../conformance/numerics/negative_shift.lt), [numerics/overflow.lt](../conformance/numerics/overflow.lt), [numerics/remainder_by_zero.lt](../conformance/numerics/remainder_by_zero.lt), [numerics/shift_amount_edges.lt](../conformance/numerics/shift_amount_edges.lt), [numerics/shift_by_width.lt](../conformance/numerics/shift_by_width.lt), [numerics/subtraction_overflow.lt](../conformance/numerics/subtraction_overflow.lt), [numerics/unsigned_shift_by_width.lt](../conformance/numerics/unsigned_shift_by_width.lt), [program/error_reached_in_function.lt](../conformance/program/error_reached_in_function.lt), [program/output_before_panic.lt](../conformance/program/output_before_panic.lt), [program/panic_in_callback.lt](../conformance/program/panic_in_callback.lt), [program/panic_in_interpolation.lt](../conformance/program/panic_in_interpolation.lt), [std/abs_of_minimum.lt](../conformance/std/abs_of_minimum.lt), [std/list_index_out_of_bounds.lt](../conformance/std/list_index_out_of_bounds.lt), [std/list_insert_out_of_bounds.lt](../conformance/std/list_insert_out_of_bounds.lt), [std/list_remove_out_of_bounds.lt](../conformance/std/list_remove_out_of_bounds.lt), [std/list_slice_out_of_bounds.lt](../conformance/std/list_slice_out_of_bounds.lt), [std/list_store_out_of_bounds.lt](../conformance/std/list_store_out_of_bounds.lt), [std/missing_key.lt](../conformance/std/missing_key.lt), [std/slice_inside_a_character.lt](../conformance/std/slice_inside_a_character.lt), [std/slice_starting_inside_a_character.lt](../conformance/std/slice_starting_inside_a_character.lt), [std/string_slice_out_of_bounds.lt](../conformance/std/string_slice_out_of_bounds.lt).

<a id="effects.overflow-effect"></a>
An operation whose only possible panic is `overflow` adds no implicit `panic` effect. It adds the implicit effect `overflow` instead, which a function inherits from the functions it names, as it inherits `panic` ([facts.inference](15-facts.md#facts.inference)). These operations add it:

- integer `+`, `-` and `*`, and their compound assignments;
- `-` on a value that isn't an integer literal ([numbers.negative-literals](06-numbers.md#numbers.negative-literals));
- `/`, `%`, `/=` and `%=` on a signed type, unless the divisor is written as an integer literal other than `-1`;
- `<<`, `>>`, `<<=` and `>>=`, unless the amount is written as an integer literal from 0 to one below the left operand's width;
- a call of an integer type's `abs`, `pow`, `gcd` or `lcm` ([std.integers](17-std.md#std.integers));
- a call of an integer type's `div_euclid` or `rem_euclid`, unless the divisor is written as an integer literal other than `0` and `-1`.

The wrapping operators ([numbers.wrapping](06-numbers.md#numbers.wrapping)) and float arithmetic add nothing. `stilt show` prints `overflow` in a function's bracket after `panic`, with the line that causes it, as it prints `panic` ([facts.visibility](15-facts.md#facts.visibility)).

Tests: [effects/without_overflow.lt](../conformance/effects/without_overflow.lt).

<a id="effects.panicking-operations"></a>
Every read of `m[k]` on a map adds `panic`, the read in `m[k] += v` included, whether or not the map has a default. It adds none when a rule of acceptance proves `k` present ([facts.keys](15-facts.md#facts.keys)). A store `m[k] = v` adds nothing of its own, and names the key type's impls of `Eq` and `Hash`, as `insert` does. Integer `/` and `%`, `/=` and `%=` included, add `panic`. They add none when the divisor is written as an integer literal other than zero, as in `n / 2`. They add none either when a rule of acceptance proves the divisor not zero ([facts.divisors](15-facts.md#facts.divisors)). An index of a list or an array adds no `panic` when a rule of acceptance proves it in range ([facts.range-loops](15-facts.md#facts.range-loops), [facts.guards](15-facts.md#facts.guards)).

Tests: [effects/natives_under_limits.lt](../conformance/effects/natives_under_limits.lt), [effects/without_panic_accepted.lt](../conformance/effects/without_panic_accepted.lt), [effects/without_panic_map_element_place.lt](../conformance/effects/without_panic_map_element_place.lt), [effects/without_panic_map_store/main.lt](../conformance/effects/without_panic_map_store/main.lt), [effects/without_panic_operations.lt](../conformance/effects/without_panic_operations.lt), [numerics/divide_by_literal_zero.lt](../conformance/numerics/divide_by_literal_zero.lt), [views/view_panics.lt](../conformance/views/view_panics.lt).

<a id="effects.without-panic"></a>
Code limited by `without panic` contains no operation that adds the implicit `panic` effect, and inherits none from the functions it names, in any module ([facts.inference](15-facts.md#facts.inference)). A module's limit covers the bodies of its functions ([program.module-header](04-programs.md#program.module-header)), and a function's limit covers its own body ([declarations.function-declarations](10-declarations.md#declarations.function-declarations)). Test bodies and doc examples are exempt, so the tests of a limited module may use `assert`. The error is E0204, *fact beyond a `without` limit*, at each operation that panics and at each operation that names a function whose implicit effects include `panic`.

A function limited by `without panic`, through its module or its own declaration, counts as one that can't panic wherever it is named, directly or through other functions. Its own panics are errors where they are written. `without panic` rules out every panic but two: an integer's overflow, which `without overflow` rules out ([effects.without-overflow](#effects.without-overflow)), and a `deadlock`, which a `when` reached through a function value or a handler's body may meet ([shared.when-on-value-already-held](14-tasks.md#shared.when-on-value-already-held)). So code that must never panic is limited by `without panic, overflow`, and holds no `Shared<T>` it doesn't see. `without panic` doesn't promise that the code ends. `without panic, div` means **total**: the code ends without a panic, unless it overflows an integer, overflows the stack or runs out of memory ([facts.without-div](15-facts.md#facts.without-div)).

Tests: [declarations/function_limits.lt](../conformance/declarations/function_limits.lt), [effects/natives_under_limits.lt](../conformance/effects/natives_under_limits.lt), [effects/without_panic_accepted.lt](../conformance/effects/without_panic_accepted.lt), [effects/without_panic_inherits/main.lt](../conformance/effects/without_panic_inherits/main.lt), [effects/without_panic_map_element_place.lt](../conformance/effects/without_panic_map_element_place.lt), [effects/without_panic_map_store/main.lt](../conformance/effects/without_panic_map_store/main.lt), [effects/without_panic_operations.lt](../conformance/effects/without_panic_operations.lt), [effects/without_panic_reported_once/main.lt](../conformance/effects/without_panic_reported_once/main.lt), [effects/without_panic_tests_assert.lt](../conformance/effects/without_panic_tests_assert.lt), [effects/without_panic_traits/main.lt](../conformance/effects/without_panic_traits/main.lt), [effects/without_panic_unwrap.lt](../conformance/effects/without_panic_unwrap.lt), [hygiene/copy_with_error.lt](../conformance/hygiene/copy_with_error.lt), [implicit/body_error_no_effects/main.lt](../conformance/implicit/body_error_no_effects/main.lt), [implicit/callees/main.lt](../conformance/implicit/callees/main.lt), [implicit/closures/main.lt](../conformance/implicit/closures/main.lt), [implicit/recursion/main.lt](../conformance/implicit/recursion/main.lt), [implicit/traits/main.lt](../conformance/implicit/traits/main.lt), [implicit/without_panic_accepted/main.lt](../conformance/implicit/without_panic_accepted/main.lt), [names/repeated_without_is_ignored.lt](../conformance/names/repeated_without_is_ignored.lt), [properties/without_panic.lt](../conformance/properties/without_panic.lt), [std/euclid_without_panic.lt](../conformance/std/euclid_without_panic.lt), [verification/divisors_rejected.lt](../conformance/verification/divisors_rejected.lt), [verification/guards_rejected.lt](../conformance/verification/guards_rejected.lt), [verification/keys_rejected.lt](../conformance/verification/keys_rejected.lt), [verification/order_effects_rejected.lt](../conformance/verification/order_effects_rejected.lt), [verification/order_rejected.lt](../conformance/verification/order_rejected.lt), [verification/range_arrays_rejected.lt](../conformance/verification/range_arrays_rejected.lt), [verification/range_loops_rejected.lt](../conformance/verification/range_loops_rejected.lt), [views/view_panics.lt](../conformance/views/view_panics.lt).

<a id="effects.without-overflow"></a>
Overflow still panics at run time under `without panic`, which doesn't rule it out. `without overflow` rules it out by the same rules, with E0204 at each operation that can overflow and at each operation that names a function that can. `overflow` is a limit and a contextual keyword, as `div` and `copy` are ([facts.spelling](15-facts.md#facts.spelling)). Code limited by `without panic, overflow` panics only with `deadlock`. Otherwise it ends early only when the process aborts, on a stack overflow or when memory runs out ([program.exit-statuses](04-programs.md#program.exit-statuses)). Verification, part of `stilt check`, proves that some operations can't overflow, and a release build drops their checks ([facts.proved-overflow](15-facts.md#facts.proved-overflow)). The proof changes nothing that `check` accepts.

Tests: [effects/natives_under_limits.lt](../conformance/effects/natives_under_limits.lt), [effects/without_overflow.lt](../conformance/effects/without_overflow.lt), [effects/without_overflow_runs.lt](../conformance/effects/without_overflow_runs.lt).

## User-defined effects

<a id="handlers.declaring-effect"></a>
`effect Name { fn op(…) -> T … }` declares an effect in the type namespace ([declarations.namespaces](10-declarations.md#declarations.namespaces)) (the `effect` and `operation` productions, [syntax.declarations](03-syntax.md#syntax.declarations)). An effect takes type parameters as a type does, as in `effect State<S> { … }`. An effect has one or more **operations**, and an effect with none is E0518, *effect with no operations*, at its name. Each operation is a function head with a name used once in the effect (E0208), parameters, a result, and a row of its own. A handler's implementation of the operation may perform that row, and the operation then performs it where it is performed. The `with` that installs the handler performs that row's effects too, since the body performs them on the handlers outside the `with` ([handlers.with](#handlers.with)). An operation has no generics, no `self`, no `inout` parameter ([handlers.no-inout-parameter](#handlers.no-inout-parameter)), no `inout` result and no body. An effect may be `pub` and take doc comments, as a type does, and the operations of a `pub` effect are its API ([versions.api](21-versions.md#versions.api)). Effects belong to the advanced tier ([handlers.advanced-tier](#handlers.advanced-tier)).

Tests: [handlers/basic.lt](../conformance/handlers/basic.lt), [handlers/no_operations.lt](../conformance/handlers/no_operations.lt), [handlers/operation_rows.lt](../conformance/handlers/operation_rows.lt), [handlers/operation_rows_unhandled.lt](../conformance/handlers/operation_rows_unhandled.lt), [ported/koka_abort.lt](../conformance/ported/koka_abort.lt).

<a id="handlers.no-inout-parameter"></a>
An operation's parameter is never `inout`. A parameter marked `inout` in the effect's declaration is E0517, *operation with an `inout` parameter*, at the parameter's name. So is one that a handler's operation marks `inout`, in place of the E0511 that its mismatch with the effect would give. An operation that changes a value takes it and returns the new one, as `fn bump(n: i64) -> i64` does. The code that performs it assigns the result: `x = Bump.bump(x)`.

Tests: [operations/inout_parameter.lt](../conformance/operations/inout_parameter.lt), [operations/values.lt](../conformance/operations/values.lt).

<a id="handlers.effects-in-rows"></a>
A row element may be an effect, `Name` or `Name<T…>`, beside `io`, `raise<E>` and a row variable, as in `/ {io, Prices}`. An `Upper` name in a row that names no effect is an unknown name (E0211). A row holds at most one instance of an effect, so `/ {State<i64>, State<str>}` is E0515, *effect given twice in a row*, at the second instance. An effect performed with other type arguments than the row's is E0311 where it is performed. A function type's row holds effects as any row does, so `fn(str) -> f64 / Prices` is the type of a function value that performs `Prices`.

Tests: [handlers/errors.lt](../conformance/handlers/errors.lt), [handlers/upper_row_element.lt](../conformance/handlers/upper_row_element.lt), [handlers/values.lt](../conformance/handlers/values.lt).

<a id="handlers.performing-operation"></a>
`Name.op(…)` **performs** the operation: it calls the implementation of the nearest handler of `Name` installed around it as the program runs ([handlers.with](#handlers.with)). Its effect is `Name`, with the type arguments that the row it must fit gives it. Where no row is declared, the first performance in evaluation order gives them, as for a closure's error type ([effects.one-error-type](#effects.one-error-type)). The performance also performs the operation's own row. A performance's effect fits its row as a call's does, so performing outside a row that holds the effect is E0502, at the first performance ([effects.inference](#effects.inference)).

Tests: [handlers/basic.lt](../conformance/handlers/basic.lt), [handlers/errors.lt](../conformance/handlers/errors.lt), [ported/effekt_nim.lt](../conformance/ported/effekt_nim.lt).

<a id="handlers.rows-pass-effects-on"></a>
An effect is an element of a row like any other. Row variables, written or implicit, carry it, and a function value with a smaller row fits a larger one ([effects.function-values](#effects.function-values)). The effects of an argument given to a non-escaping parameter pass through to the caller ([effects.non-escaping-parameters](#effects.non-escaping-parameters)). So a function passed to `map` performs its caller's effects, as it performs `io` and `raise<E>`.

Tests: [handlers/basic.lt](../conformance/handlers/basic.lt), [handlers/rows.lt](../conformance/handlers/rows.lt), [ported/effekt_nim.lt](../conformance/ported/effekt_nim.lt), [ported/effekt_stream_push.lt](../conformance/ported/effekt_stream_push.lt).

<a id="handlers.advanced-tier"></a>
A module is in the advanced tier ([program.module-tier](04-programs.md#program.module-tier)) when it does any of these:

- declares an effect;
- writes an effect in a row or a type;
- performs an operation;
- writes a handler or a `with`.

A module that only calls a function declared elsewhere whose row holds no effect of its own stays in its tier.

Checked by: the facts suite, whose `tests/facts/handlers.lt` carries `//~ tier: advanced`, which `just facts` checks (`compiler/stilt-cli/tests/facts.rs`).

## Handlers

<a id="handlers.handler-literals"></a>
A **handler** is a value that implements each operation of an effect `Name` once. Its literal is `handler Name { fn op(…) -> T { body } … }`, or `handler Name -> R { … }` for a handler that takes control ([handlers.resuming](#handlers.resuming)). Each operation has the parameter and result types that the effect declares, with the effect's type arguments substituted, which the literal writes or inference gives. Each of these is E0511, *handler that doesn't match its effect*:

- an operation missing, or implemented twice;
- an operation that the effect doesn't declare;
- an operation with other types, among them one written with type parameters, a `where` clause or a `without` limit, which no operation of an effect has ([syntax.declarations](03-syntax.md#syntax.declarations));
- a handler literal of `async` ([tasks.async](14-tasks.md#tasks.async)).

A handler captures the bindings its bodies name as a closure literal does, by copy when it is made ([expressions.capture](08-expressions.md#expressions.capture)). Its bodies may perform the effects of their operations' rows, and those of the handler's type ([handlers.handler-types](#handlers.handler-types)). Anything more is E0502 in the body: a raise, or a declared effect, that the operation's row doesn't hold.

Tests: [handlers/basic.lt](../conformance/handlers/basic.lt), [handlers/body_effects.lt](../conformance/handlers/body_effects.lt), [handlers/body_io.lt](../conformance/handlers/body_io.lt), [handlers/body_panics_after_printing.lt](../conformance/handlers/body_panics_after_printing.lt), [handlers/body_raises_after_printing.lt](../conformance/handlers/body_raises_after_printing.lt), [handlers/errors.lt](../conformance/handlers/errors.lt), [handlers/operation_forms.lt](../conformance/handlers/operation_forms.lt), [handlers/values.lt](../conformance/handlers/values.lt).

<a id="handlers.handler-types"></a>
A handler's type is written as its literal begins, `handler Name` or `handler Name -> R`, followed by a row, as in `handler Log / io`. That row is what the handler's bodies perform beyond their operations' rows: `io`, what its captures perform, and its own effect, which its bodies perform on the handler outside it. A `with` that installs the handler performs that row. A handler is a value, passed, stored and returned as a function value is. A parameter of handler type is always non-escaping. Installing it with `with` is a use it may have, as a call is, and the effects of its type pass through to the caller ([effects.non-escaping-parameters](#effects.non-escaping-parameters)). A handler that must be kept is a field's or a local's value.

Tests: [handlers/answer_types.lt](../conformance/handlers/answer_types.lt), [handlers/body_effects.lt](../conformance/handlers/body_effects.lt), [handlers/body_io.lt](../conformance/handlers/body_io.lt), [handlers/values.lt](../conformance/handlers/values.lt), [ported/effekt_rethrow.lt](../conformance/ported/effekt_rethrow.lt), [ported/koka_handler_context.lt](../conformance/ported/koka_handler_context.lt), [views/view_types_in_signatures.lt](../conformance/views/view_types_in_signatures.lt).

<a id="handlers.with"></a>
`with h { block }` evaluates `h`, installs it for the length of `block`, and evaluates `block`, whose value is the `with`'s. `with a, b { … }` is `with a { with b { … } }`. A performance inside the block, at any depth of calls, calls the nearest handler of its effect installed when the performance runs. So a handler installed inside another of the same effect hides it, and a handler's own bodies perform its effect on the handler outside it. The `with` performs the block's effects without the handler's effect, together with the effects of the handler's type and the effects that its operations' rows hold. A raise or `io` in an operation's row is the performance's alone. A handler is installed only while its block runs. A closure that performs the effect and is called after the block ends needs a handler where it is called, as its type says.

Tests: [handlers/basic.lt](../conformance/handlers/basic.lt), [handlers/context.lt](../conformance/handlers/context.lt), [handlers/later.lt](../conformance/handlers/later.lt), [handlers/leaving.lt](../conformance/handlers/leaving.lt), [handlers/operation_rows.lt](../conformance/handlers/operation_rows.lt), [handlers/operation_rows_unhandled.lt](../conformance/handlers/operation_rows_unhandled.lt), [handlers/raise_past_resume.lt](../conformance/handlers/raise_past_resume.lt), [handlers/values.lt](../conformance/handlers/values.lt), [ported/effekt_abort_inside_handler.lt](../conformance/ported/effekt_abort_inside_handler.lt), [ported/effekt_loops.lt](../conformance/ported/effekt_loops.lt), [ported/effekt_multihandler.lt](../conformance/ported/effekt_multihandler.lt), [ported/effekt_nim.lt](../conformance/ported/effekt_nim.lt), [ported/effekt_rethrow.lt](../conformance/ported/effekt_rethrow.lt), [ported/effekt_stream_push.lt](../conformance/ported/effekt_stream_push.lt), [ported/koka_handler_context.lt](../conformance/ported/koka_handler_context.lt), [ported/koka_resume_inside_with.lt](../conformance/ported/koka_resume_inside_with.lt), [types/loop_break_in_with.lt](../conformance/types/loop_break_in_with.lt), [verification/order_effects_rejected.lt](../conformance/verification/order_effects_rejected.lt), [verification/order_ended.lt](../conformance/verification/order_ended.lt), [verification/order_ended_through.lt](../conformance/verification/order_ended_through.lt).

<a id="handlers.resuming"></a>
A handler written `handler Name { … }` resumes every performance with its operation's value: the performance's value is the body's, and the program goes on from it. A handler written `handler Name -> R { … }` **takes control** in each of its operations. In such a body, `resume(v)` resumes the performance, with `v` of the operation's result type, or `resume()` for `()`. The value of `resume` is the value of the rest of the `with`'s block, of type `R`, once that rest ends, and the body may then go on. A rest that ends otherwise, by a raise or a jump that leaves the `with`, ends the `with` so, and a body that waits at its `resume` never goes on: `resume` raises nothing, as its type says. The rest of the block runs under the handlers installed around the performance, never under one that the body installs around its `resume`. The body's value, of type `R`, is the `with`'s value, so the `with`'s block has type `R` too (E0311). A path of the body that doesn't resume ends the `with` with the body's value, and the rest of the block never runs. A `resume` statement is no unused value ([expressions.unused-values](08-expressions.md#expressions.unused-values)).

Tests: [handlers/context.lt](../conformance/handlers/context.lt), [handlers/errors.lt](../conformance/handlers/errors.lt), [handlers/leaving.lt](../conformance/handlers/leaving.lt), [handlers/raise_past_resume.lt](../conformance/handlers/raise_past_resume.lt), [handlers/resuming.lt](../conformance/handlers/resuming.lt), [ported/effekt_abort_inside_handler.lt](../conformance/ported/effekt_abort_inside_handler.lt), [ported/effekt_abort_past_var.lt](../conformance/ported/effekt_abort_past_var.lt), [ported/effekt_loops.lt](../conformance/ported/effekt_loops.lt), [ported/effekt_rethrow.lt](../conformance/ported/effekt_rethrow.lt), [ported/effekt_stream_pull.lt](../conformance/ported/effekt_stream_pull.lt), [ported/effekt_stream_push.lt](../conformance/ported/effekt_stream_push.lt), [ported/koka_abort.lt](../conformance/ported/koka_abort.lt), [ported/koka_linear_state.lt](../conformance/ported/koka_linear_state.lt), [ported/koka_resume_inside_with.lt](../conformance/ported/koka_resume_inside_with.lt), [shared/when_left_by_handler.lt](../conformance/shared/when_left_by_handler.lt).

<a id="handlers.resume-at-most-once"></a>
A body resumes at most once on each path. A `resume` is E0514, *operation that may resume twice*, in each of these places:

- in a loop;
- in a closure literal;
- after another `resume` in sequence;
- in a branch that runs after another that resumed.

No closure holds a `resume`, so a performance, the body that takes it and its `resume` run in one task ([tasks.continuations-stay-in-task](14-tasks.md#tasks.continuations-stay-in-task)).

Tests: [handlers/errors.lt](../conformance/handlers/errors.lt).

<a id="handlers.resume-outside-operation"></a>
`resume` anywhere but in the body of an operation of a handler written with `-> R` is E0513, *`resume` outside a handler's operation*. This holds in a handler nested in that body too.

Tests: [handlers/errors.lt](../conformance/handlers/errors.lt).

<a id="handlers.with-pairing"></a>
A `with` handles every performance of its effect that reaches it, as a `catch` handles every raise ([effects.innermost-catch](#effects.innermost-catch)). Take a call in a `with`'s block whose callee's row, as instantiated at the call, holds a row variable `v` of the enclosing function. The call is E0516, *handler around an effect that belongs to the caller*, unless the row also holds the effect and the enclosing signature pairs `v` with it. The error is at the call. The rule has the exceptions that [effects.catch-around-row-variables](#effects.catch-around-row-variables) gives a `catch`'s operand. A signature pairs a row variable with each effect that a row of it holds beside the variable. [effects.passing-to-paired-variables](#effects.passing-to-paired-variables) and [effects.what-paired-variable-may-raise](#effects.what-paired-variable-may-raise) apply to effects as to error types.

Tests: [handlers/errors.lt](../conformance/handlers/errors.lt), [handlers/rows.lt](../conformance/handlers/rows.lt).

<a id="handlers.no-effect-reaches-main"></a>
The row of `main` holds no user-defined effect ([program.main](04-programs.md#program.main)), and neither does a test's body or a doc example's ([program.test-declarations](04-programs.md#program.test-declarations)). So every performance in a program runs under a handler. A row of `main` that holds one is E0512, *effect that reaches `main`*, at the effect in the row. So is the first performance that a test, a doc example or `main` makes outside every `with` of its effect, in place of the E0502 that [handlers.performing-operation](#handlers.performing-operation) would give.

Tests: [handlers/main_effect.lt](../conformance/handlers/main_effect.lt), [handlers/operation_rows_unhandled.lt](../conformance/handlers/operation_rows_unhandled.lt).

<a id="handlers.implicit-effects-and-capabilities"></a>
A handler literal's bodies are code of the function that writes it, as a closure literal's are ([facts.inference](15-facts.md#facts.inference), [facts.capabilities](15-facts.md#facts.capabilities)). Performing an operation is a call through a stored function value. It adds no `panic`, `copy` or capability ([facts.calls-through-function-values](15-facts.md#facts.calls-through-function-values)), and it is a site of `div` ([facts.div](15-facts.md#facts.div)) and of `alloc`, for the rest of the performance that a handler may keep to resume ([facts.allocation](15-facts.md#facts.allocation)). A `with` allocates the handler it installs, and adds nothing else of its own.

Tests: [implicit/allocating_natives.lt](../conformance/implicit/allocating_natives.lt).

Checked by: the facts suite, whose `tests/facts/handlers.lt` gives a handler's bodies' facts to the function that writes it and `div` to a performance, which `just facts` checks (`compiler/stilt-cli/tests/facts.rs`).

## Calls that a handler ends

<a id="handlers.call-that-handler-ends"></a>
When the body of an operation ends its `with` without resuming, every call running between the performance and the `with` ends there, innermost first. Each call ends as it would if the performance raised. The code after the performance never runs. Each `inout` argument holds every change the callee made before the performance, written back as on a raise ([values.inout-arguments](05-values.md#values.inout-arguments)).

Tests: [ended/calls.lt](../conformance/ended/calls.lt), [ported/effekt_abort_inside_handler.lt](../conformance/ported/effekt_abort_inside_handler.lt), [ported/effekt_abort_past_var.lt](../conformance/ported/effekt_abort_past_var.lt), [ported/effekt_stream_pull.lt](../conformance/ported/effekt_stream_pull.lt), [verification/order_effects_rejected.lt](../conformance/verification/order_effects_rejected.lt), [verification/order_ended_through.lt](../conformance/verification/order_ended_through.lt).

<a id="handlers.ended-projections"></a>
A projection whose caller's access a handler ends doesn't resume, as when the access raises ([projections.raising-during-access](13-modes.md#projections.raising-during-access)). The statements after its `yield` don't run, and the place it yielded holds what the access wrote before the performance.

Tests: [ended/projections.lt](../conformance/ended/projections.lt).

<a id="handlers.when-place-is-seen"></a>
A handler's body can't reach a place of the calls it ends. Their `inout` arguments are places of the code that called them. The body has only its operation's arguments, which are values, and its captures, which are copies. So whether such a place is written back before or after the body runs can't be observed, and the first code that sees it runs after the `with`.

Tests: [ended/calls.lt](../conformance/ended/calls.lt).

<a id="handlers.resuming-keeps-exclusivity"></a>
A handler's body reaches no place of the code that performed its operation. Its arguments are values ([handlers.no-inout-parameter](#handlers.no-inout-parameter)), and its captures are copies made when the handler is made. So no access of the body overlaps an access of the code it suspends, before or after `resume`. The law of exclusivity ([modes.law](13-modes.md#modes.law)) holds across a resumption with no rule of its own.

Tests: [operations/values.lt](../conformance/operations/values.lt).
