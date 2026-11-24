# 9. Patterns

A pattern matches a value by its shape and binds names to its parts. Patterns stand in `match` and `catch` arms, `if let`, `let` and `var` statements, `for` heads and closure parameters, and every `match` must cover every value of its type. The variants and constants that patterns name are declared as [Declarations](10-declarations.md) says. `match`, `if let` and the `else` fallback are expressions of [Expressions](08-expressions.md), and the copies that bindings make are those of [The value model](05-values.md).

## Forms

<a id="patterns.pattern-forms"></a>
A pattern is one of these forms, as the `pattern` production writes them ([syntax.patterns](03-syntax.md#syntax.patterns)):

| Form | Matches |
| --- | --- |
| `_` | Anything, and binds nothing |
| `x`, a `lower` name | Anything, and binds it to `x` |
| A literal: an integer, optionally negative ([numbers.negative-literals](06-numbers.md#numbers.negative-literals)), a string with no interpolation, `true`, `false` or `()` | Equal values |
| A constant: `C`, `m.C` or `Type.NAME` | Values equal to the constant ([patterns.constants](#patterns.constants)) |
| `(p₁, …, pₙ)` | Tuples, element by element |
| A variant: `V`, `V(p₁, …, pₙ)`, `m.V` or `m.V(p₁, …, pₙ)` | That variant, with its payload fields matched by position |
| `T { f: p, g, .. }` or `m.T { … }` | Records of type `T`. A bare `g` binds the field `g`, and `..` ignores the fields not listed |
| `[p₁, …, pₙ]` | Lists of exactly `n` elements |
| `[p₁, …, pₙ, ..]` and `[p₁, …, pₙ, ..rest]` | Lists of at least `n` elements. `rest` binds the remaining elements as a `List` |
| `p₁ \| p₂` | Either alternative ([patterns.or-patterns](#patterns.or-patterns)) |

An uppercase name is never a binding: it names a variant or a constant ([lexical.case](02-lexical.md#lexical.case)). So where nothing is called `Total`, `let Total = 1` is E0211, *unknown name*. A list pattern also matches an array whose size fits it ([generics.array-patterns](07-types.md#generics.array-patterns)). `{ f, .. }` matches an anonymous record, and a value of a type with a record bound ([records.anonymous-patterns](07-types.md#records.anonymous-patterns)).

Tests: [expressions/if_let_chains.lt](../conformance/expressions/if_let_chains.lt), [lexical/uppercase_binding.lt](../conformance/lexical/uppercase_binding.lt), [numerics/negative_literals.lt](../conformance/numerics/negative_literals.lt), [numerics/negative_literals_rejected.lt](../conformance/numerics/negative_literals_rejected.lt), [patterns/pattern_forms.lt](../conformance/patterns/pattern_forms.lt), [patterns/qualified_patterns](../conformance/patterns/qualified_patterns/), [patterns/unit_pattern.lt](../conformance/patterns/unit_pattern.lt), [ported/fizzbuzz.lt](../conformance/ported/fizzbuzz.lt), [types/unsigned_negation.lt](../conformance/types/unsigned_negation.lt).

<a id="patterns.pattern-types"></a>
A pattern is checked against the type of the value it matches. A form that the values of that type can't have is E0311, *mismatched types*, as a tuple pattern matched against an `i64` is. A variant pattern must give as many payload patterns as the variant has payload fields, or it is E0315, *wrong number of arguments*. A record pattern without `..` must name every field of its record, as a struct literal gives each ([expressions.struct-literal-fields](08-expressions.md#expressions.struct-literal-fields)), or it is E0316, *field given twice or left out*. The names that one pattern binds must be distinct, or it is E0208, *name defined twice* ([declarations.unique-names](10-declarations.md#declarations.unique-names)).

Tests: [checking/resolution_errors.lt](../conformance/checking/resolution_errors.lt), [patterns/qualified_pattern_errors](../conformance/patterns/qualified_pattern_errors/), [types/argument_counts.lt](../conformance/types/argument_counts.lt), [types/failed_shapes.lt](../conformance/types/failed_shapes.lt), [types/fields.lt](../conformance/types/fields.lt).

<a id="patterns.no-other-forms"></a>
No other form is a pattern. Each of these is E0100, *syntax error*:

- a string with an interpolation
- a range, such as `1..=9`
- a binding with `@`, as in `kept @ Some(_)`
- a list pattern with a pattern after its `..`, as in `[.., last]`

Tests: [patterns/at_binding.lt](../conformance/patterns/at_binding.lt), [patterns/interpolated_pattern.lt](../conformance/patterns/interpolated_pattern.lt), [patterns/range_pattern.lt](../conformance/patterns/range_pattern.lt).

<a id="patterns.floats"></a>
Only `_` and a binding match a float, and no literal pattern is a float. An integer literal matched against a float is E0328, *float in a pattern*. So is a constant whose type can hold a float, itself or in its elements, fields or payloads. A constant of type `f64` is one, and so is a constant of a record with an `f64` field.

Tests: [patterns/float_patterns.lt](../conformance/patterns/float_patterns.lt), [patterns/qualified_pattern_errors](../conformance/patterns/qualified_pattern_errors/).

<a id="patterns.or-patterns"></a>
In `p₁ | p₂`, every alternative must bind the same names as the first, with the same types. An alternative that binds other names than the first is E0217, *alternatives bind different names*, at that alternative. An alternative that binds a name with another type is E0311, *mismatched types*. A name that only some alternatives bind has the error type wherever it is used or bound again, so it causes no further diagnostic ([errors.error-type](18-errors.md#errors.error-type)).

Tests: [checking/resolution_errors.lt](../conformance/checking/resolution_errors.lt), [expressions/bar_token.lt](../conformance/expressions/bar_token.lt), [names/or_pattern_names.lt](../conformance/names/or_pattern_names.lt), [patterns/or_pattern_types.lt](../conformance/patterns/or_pattern_types.lt), [ported/balanced_brackets.lt](../conformance/ported/balanced_brackets.lt).

## Constants

<a id="patterns.constants"></a>
A constant pattern, `C`, `m.C` or `Type.NAME` ([declarations.constants-in-patterns](10-declarations.md#declarations.constants-in-patterns)), matches the values that are structurally equal to the value of the constant. Two values are **structurally equal** when they are equal part by part, as the structural impls compare them ([traits.structural-calls](11-traits.md#traits.structural-calls)).

Tests: [declarations/constants](../conformance/declarations/constants/), [patterns/constant_with_automatic_eq.lt](../conformance/patterns/constant_with_automatic_eq.lt), [patterns/pattern_forms.lt](../conformance/patterns/pattern_forms.lt), [patterns/structured_constants.lt](../conformance/patterns/structured_constants.lt).

<a id="patterns.constants-with-written-eq"></a>
A constant is not a pattern when its type holds, at any depth, a type whose `Eq` impl the program writes. That type may be the constant's type itself, one of its type arguments, or the type of one of its fields or payloads. A constant like this used as a pattern is E0331, *constant with a written `Eq` in a pattern*. The rule goes by the type, not the value: with the `Eq` of `Name` written, `const NOBODY: Option<Name> = None` is not a pattern either. A guard may compare such a constant instead, as in `n if n == NOBODY`.

Tests: [patterns/constant_component_with_written_eq.lt](../conformance/patterns/constant_component_with_written_eq.lt), [patterns/constant_none_with_written_eq.lt](../conformance/patterns/constant_none_with_written_eq.lt), [patterns/constant_with_automatic_eq.lt](../conformance/patterns/constant_with_automatic_eq.lt), [patterns/constant_with_written_eq.lt](../conformance/patterns/constant_with_written_eq.lt).

## Variants named by the matched type

<a id="patterns.variants-by-type"></a>
In a pattern, a bare variant name, `V` or `V(p₁, …)`, names a variant of the type that the pattern is matched against, whatever module declares that type. It does so when that type is known there, by its outermost constructor ([types.known-types](07-types.md#types.known-types)), to be a variant type with a variant `V`. This meaning comes before every other meaning of `V`, including a variant or a constant of the module's own and a prelude variant. So with `e: ebnf.Expr`, `match e { Seq(items) => … }` reads `Seq` as `ebnf.Seq`.

Otherwise `V` is resolved as any name is ([declarations.name-lookup](10-declarations.md#declarations.name-lookup)), and a qualified `m.V` names the item of `m`. The rule holds in every pattern: `match` and `catch` arms, `if let`, `let` and `var` with or without `else`, `for` heads and closure parameters. It holds in nested patterns too, which are matched against the types of the payloads, fields and elements around them. An expression still names a variant of another module with its module, as in `ebnf.Seq(xs)` ([declarations.qualified-variants](10-declarations.md#declarations.qualified-variants)).

Tests: [patterns/bare_variant_if_let](../conformance/patterns/bare_variant_if_let/), [patterns/bare_variant_positions](../conformance/patterns/bare_variant_positions/), [patterns/bare_variants](../conformance/patterns/bare_variants/), [patterns/else_through_tuple](../conformance/patterns/else_through_tuple/), [patterns/prelude_variant_through_type.lt](../conformance/patterns/prelude_variant_through_type.lt), [ported/balanced_brackets.lt](../conformance/ported/balanced_brackets.lt).

<a id="patterns.unknown-variants"></a>
If the matched type is known to be a variant type, a bare name that is none of its variants and no name in scope is E0211, *unknown name*, at the name. It is the same error as for any name that resolves to nothing ([declarations.unknown-names](10-declarations.md#declarations.unknown-names)). A pattern whose type isn't known where it stands reads its names as any name is read. A closure parameter with no expected type is such a pattern, so `|Lit(s)| s.len()` is E0211 when the module has no `Lit`.

Tests: [patterns/bare_variant_errors](../conformance/patterns/bare_variant_errors/).

## Bindings

<a id="patterns.bindings-are-copies"></a>
A binding copies the part of the value it matched, and the copy is independent of the value ([values.independent-copies](05-values.md#values.independent-copies)).

Tests: [expressions/if_let_loops.lt](../conformance/expressions/if_let_loops.lt), [patterns/bindings_are_copies.lt](../conformance/patterns/bindings_are_copies.lt), [values/independent_copies.lt](../conformance/values/independent_copies.lt).

<a id="patterns.var-bindings"></a>
A `var` statement makes every binding of its pattern mutable, as in `var (a, b) = pair` ([values.let-and-var](05-values.md#values.let-and-var)). Bindings made anywhere else are immutable: those of `let`, of `match`, `catch` and `if let` arms, of `for` heads and of closure parameters. Modifying an immutable binding is E0403, *modifying what can't be modified* ([modes.what-can-be-modified](13-modes.md#modes.what-can-be-modified)). `var x = x` makes a mutable copy of one ([expressions.shadowing](08-expressions.md#expressions.shadowing)).

Tests: [modes/read_only_bindings.lt](../conformance/modes/read_only_bindings.lt), [modes/rebinding.lt](../conformance/modes/rebinding.lt), [modes/var_patterns.lt](../conformance/modes/var_patterns.lt), [patterns/bindings_immutable.lt](../conformance/patterns/bindings_immutable.lt).

## Refutability

<a id="patterns.irrefutable-positions"></a>
A pattern is **irrefutable** when its form alone guarantees a match. These patterns are irrefutable:

- `_`, a binding and `()`
- a tuple or record pattern whose parts are irrefutable
- a variant of a type with a single variant, whose payload patterns are irrefutable
- `[..]` and `[..rest]`
- an or-pattern with an irrefutable alternative

A list pattern on an array is irrefutable when its elements are ([generics.array-exhaustiveness](07-types.md#generics.array-exhaustiveness)). Every other pattern is **refutable**, even one that matches every value, as `A(x) | B(x)` does for a type whose only variants are `A` and `B`.

The patterns of `let` and `var` without `else`, of `for` heads and of closure parameters must be irrefutable. A refutable pattern there is E0321, *refutable pattern*. A closure parameter marked `inout` is a name, not a pattern ([expressions.inout-closure-parameters](08-expressions.md#expressions.inout-closure-parameters)).

Tests: [expressions/closure_forms.lt](../conformance/expressions/closure_forms.lt), [expressions/closure_inout_not_a_pattern.lt](../conformance/expressions/closure_inout_not_a_pattern.lt), [patterns/bare_variant_errors](../conformance/patterns/bare_variant_errors/), [patterns/bare_variant_positions](../conformance/patterns/bare_variant_positions/), [patterns/else_through_tuple](../conformance/patterns/else_through_tuple/), [patterns/irrefutable_positions.lt](../conformance/patterns/irrefutable_positions.lt), [patterns/refutable_patterns.lt](../conformance/patterns/refutable_patterns.lt), [patterns/refutable_positions.lt](../conformance/patterns/refutable_positions.lt), [patterns/unit_pattern.lt](../conformance/patterns/unit_pattern.lt), [patterns/var_refutable.lt](../conformance/patterns/var_refutable.lt), [ported/digital_root.lt](../conformance/ported/digital_root.lt).

<a id="patterns.let-else"></a>
`let P = e else x` is a **let-else** when `P` is refutable, and so is `var P = e else x`, whose bindings are mutable. When the value of `e` matches `P`, the bindings of `P` are in scope after the statement ([expressions.scope](08-expressions.md#expressions.scope)). Otherwise `x` runs. `x` must have type `Never` ([declarations.never](10-declarations.md#declarations.never)): it returns, raises, breaks, continues or calls a function such as `panic`. A branch of another type is E0311, *mismatched types*, as in `let Some(n) = o else 0`.

Tests: [expressions/else_fallback_types.lt](../conformance/expressions/else_fallback_types.lt), [patterns/let_else.lt](../conformance/patterns/let_else.lt), [patterns/let_else_errors.lt](../conformance/patterns/let_else_errors.lt), [patterns/var_let_else.lt](../conformance/patterns/var_let_else.lt).

<a id="patterns.else-after-pattern"></a>
The bare variant names of `P` in `let P = e else x` and `var P = e else x` decide whether `P` is refutable. They are read against the type of the annotation, if there is one, and otherwise against the type of `e`. A refutable `P` makes a let-else ([patterns.let-else](#patterns.let-else)). An irrefutable `P` makes the statement `let P = (e else x)`, or `var P = (e else x)`, the `Option` fallback ([expressions.option-fallback](08-expressions.md#expressions.option-fallback)). `P` is then matched against the type of `e else x`, where it must be irrefutable, or it is E0321.

For example, `units` declares `type Length = | Meters(f64)`, and `found` has type `Option<units.Length>`. Then `let Meters(m) = found else units.Meters(0.0)` is the fallback, because `Option` has no variant `Meters`, and `Meters(m)` matches the `Length` inside.

Tests: [expressions/else_fallback.lt](../conformance/expressions/else_fallback.lt), [patterns/bare_variant_positions](../conformance/patterns/bare_variant_positions/), [patterns/else_through_tuple](../conformance/patterns/else_through_tuple/), [patterns/let_else.lt](../conformance/patterns/let_else.lt), [reflection/let_else_on_a_shape.lt](../conformance/reflection/let_else_on_a_shape.lt).

## Matching

<a id="patterns.match"></a>
A `match` tries its arms in order. It takes the first arm whose pattern matches the value and whose guard, if it has one, is true ([patterns.guards](#patterns.guards)). The names that the arm's pattern binds are in scope in its guard and its body ([expressions.scope](08-expressions.md#expressions.scope)). The pattern of an `if let` ([expressions.if-let](08-expressions.md#expressions.if-let)) may be refutable, and is matched as an arm without a guard. It takes no part in exhaustiveness.

Tests: [expressions/if_let.lt](../conformance/expressions/if_let.lt), [expressions/if_let_chains.lt](../conformance/expressions/if_let_chains.lt), [expressions/if_let_loops.lt](../conformance/expressions/if_let_loops.lt), [expressions/if_let_types.lt](../conformance/expressions/if_let_types.lt), [expressions/match_arms.lt](../conformance/expressions/match_arms.lt), [patterns/bare_variant_if_let](../conformance/patterns/bare_variant_if_let/), [patterns/match_arms.lt](../conformance/patterns/match_arms.lt), [ported/fizzbuzz.lt](../conformance/ported/fizzbuzz.lt).

<a id="patterns.guards"></a>
An arm with a guard, `pattern if c`, matches only when its pattern matches and `c` is `true` ([expressions.conditions](08-expressions.md#expressions.conditions)). When the pattern holds or-patterns, the guard is tried with each way that the pattern matches, until it is true. The alternatives of an or-pattern are taken from left to right. Of several or-patterns, the alternatives of the leftmost vary slowest.

So `[x, ..] | [_, x, ..] if x > 10` matches `[5, 30]`, with `x` bound to `30`. For `([x, ..] | [_, x, ..], [y, ..] | [_, y, ..]) if p(x, y)`, the guard first sees the first element of each list. It then sees the first element of the first list with the second element of the second. A guard may therefore run more than once, with its effects each time.

Tests: [patterns/guard_alternatives.lt](../conformance/patterns/guard_alternatives.lt), [patterns/guard_over_two_or_patterns.lt](../conformance/patterns/guard_over_two_or_patterns.lt), [patterns/match_arms.lt](../conformance/patterns/match_arms.lt), [ported/ackermann.lt](../conformance/ported/ackermann.lt), [verification/order_popped_twice.lt](../conformance/verification/order_popped_twice.lt).

<a id="patterns.arm-types"></a>
The arms of a `match` have a common type, and an arm of type `Never` agrees with any type. Without an expected type, the first arm whose type isn't `Never` sets the type. Each later arm is checked against it ([types.expected-types](07-types.md#types.expected-types)), so a mismatch is E0311, *mismatched types*, in the later arm.

Tests: [expressions/branch_blocks.lt](../conformance/expressions/branch_blocks.lt), [patterns/arm_types.lt](../conformance/patterns/arm_types.lt).

<a id="patterns.empty-matches"></a>
A `match` on a value of a type with no values ([patterns.types-without-values](#patterns.types-without-values)), such as `Never`, may have no arms, as in `match n {}`. A `match` with no arms on a type with values is E0329, *patterns that don't cover every value*.

Tests: [effects/empty_catch.lt](../conformance/effects/empty_catch.lt), [patterns/empty_match_on_tuple_without_values.lt](../conformance/patterns/empty_match_on_tuple_without_values.lt), [patterns/empty_match_with_values.lt](../conformance/patterns/empty_match_with_values.lt), [patterns/empty_match_without_values.lt](../conformance/patterns/empty_match_without_values.lt), [patterns/uninhabited.lt](../conformance/patterns/uninhabited.lt), [patterns/uninhabited_fields.lt](../conformance/patterns/uninhabited_fields.lt).

## Exhaustiveness

<a id="patterns.algorithm"></a>
The arms of every `match` must cover every value of its type. Maranget's usefulness algorithm ("Warnings for pattern matching", 2007) decides whether they do, over these constructors of each type:

| Type | Constructors |
| --- | --- |
| Variant types | The declared variants |
| `bool` | `true` and `false` |
| `()` | A single constructor |
| Tuples and records | A single constructor each |
| Lists | One per length: `[p₁, …, pₙ]` is the constructor of length `n`, and `[p₁, …, pₙ, ..]` covers every length of at least `n` |
| Integers and strings | Infinitely many, so only `_` or a binding makes a match on them exhaustive |
| Floats | None: only `_` or a binding matches a float |

An array of size `k` counts as a tuple of `k` elements ([generics.array-exhaustiveness](07-types.md#generics.array-exhaustiveness)).

Tests: [patterns/exhaustive_constructors.lt](../conformance/patterns/exhaustive_constructors.lt), [patterns/exhaustiveness.lt](../conformance/patterns/exhaustiveness.lt), [patterns/list_lengths.lt](../conformance/patterns/list_lengths.lt), [patterns/pattern_forms.lt](../conformance/patterns/pattern_forms.lt).

<a id="patterns.types-without-values"></a>
A constructor counts only if it can build a value, and a constructor with a field of a type that has no values can't. So a match on an `Option<Never>` is exhaustive with `None` alone, and an arm `Some(_)` after it can never match. Which types have values follows these rules:

- `Never` has no values.
- A tuple has values when all its elements do.
- Every other type that the program doesn't declare has values: numbers, `bool`, `str`, `()`, lists, maps, function types and type parameters, even `List<Never>` and `fn() -> Never`.
- A declared variant type has values when one of its variants has no payload, or a payload whose types all have values.
- A declared record has values when the types of all its fields have values.

The declared types with values are the smallest set that these rules describe. So `type Loop = | Loop(Loop)` has no values, as `Never` has none.

Tests: [patterns/uninhabited.lt](../conformance/patterns/uninhabited.lt), [patterns/uninhabited_fields.lt](../conformance/patterns/uninhabited_fields.lt), [patterns/uninhabited_recursive_variant.lt](../conformance/patterns/uninhabited_recursive_variant.lt).

<a id="patterns.guards-and-constants"></a>
An arm with a guard covers nothing for exhaustiveness, and neither does an arm whose pattern holds a constant. So a `match` on an `i64` whose arms are `x if x > 0` and `x if x <= 0` doesn't cover every value. Neither does a `match` that names every variant of a type through constants. Such an arm makes no later arm unreachable either ([patterns.unreachable-arms](#patterns.unreachable-arms)).

Tests: [effects/catch_covers_error.lt](../conformance/effects/catch_covers_error.lt), [patterns/guards_and_constants.lt](../conformance/patterns/guards_and_constants.lt), [patterns/match_arms.lt](../conformance/patterns/match_arms.lt), [patterns/unreachable_constants.lt](../conformance/patterns/unreachable_constants.lt).

<a id="patterns.non-exhaustive-matches"></a>
Arms that cover every value of their type are **exhaustive**. A `match` whose arms aren't exhaustive is E0329, *patterns that don't cover every value*, at the `match`, and the diagnostic names one missing pattern as a witness. So are the arms of a `catch` that don't cover its error type ([effects.catch-syntax](12-effects.md#effects.catch-syntax)), at the `try`, so `catch {}` handles only `Never`.

A pattern on a part of the value whose type is the error type covers that part. So a mistake in a type gives no further diagnostic in the matches on it. The check runs with the analyses of a body, once its types have no error ([errors.phases](18-errors.md#errors.phases)).

Tests: [checking/error_type_in_try_and_match.lt](../conformance/checking/error_type_in_try_and_match.lt), [checking/phases.lt](../conformance/checking/phases.lt), [checking/unmodifiable_with_missing_arm.lt](../conformance/checking/unmodifiable_with_missing_arm.lt), [effects/catch_covers_error.lt](../conformance/effects/catch_covers_error.lt), [effects/empty_catch.lt](../conformance/effects/empty_catch.lt), [patterns/error_payloads.lt](../conformance/patterns/error_payloads.lt), [patterns/exhaustive_constructors.lt](../conformance/patterns/exhaustive_constructors.lt), [patterns/exhaustiveness.lt](../conformance/patterns/exhaustiveness.lt), [patterns/guards_and_constants.lt](../conformance/patterns/guards_and_constants.lt), [patterns/list_lengths.lt](../conformance/patterns/list_lengths.lt), [patterns/nested_record_witnesses.lt](../conformance/patterns/nested_record_witnesses.lt).

<a id="patterns.unreachable-arms"></a>
An arm that can never match is an **unreachable arm**, the warning W0301, at its pattern. An arm can never match when its pattern, with each constant in it read as `_`, matches no value that the earlier arms without guards or constants leave. An arm that holds a pattern on a part of the value whose type is the error type is never reported, and makes no later arm unreachable.

Tests: [effects/catch_all_forms.lt](../conformance/effects/catch_all_forms.lt), [effects/empty_try_arms.lt](../conformance/effects/empty_try_arms.lt), [patterns/broken_module_in_pattern.lt](../conformance/patterns/broken_module_in_pattern.lt), [patterns/error_payloads.lt](../conformance/patterns/error_payloads.lt), [patterns/shadowed_prelude_name_in_pattern.lt](../conformance/patterns/shadowed_prelude_name_in_pattern.lt), [patterns/uninhabited.lt](../conformance/patterns/uninhabited.lt), [patterns/uninhabited_fields.lt](../conformance/patterns/uninhabited_fields.lt), [patterns/unreachable_arms.lt](../conformance/patterns/unreachable_arms.lt), [patterns/unreachable_constants.lt](../conformance/patterns/unreachable_constants.lt).
