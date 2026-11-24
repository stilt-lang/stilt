# 6. Numbers

This chapter gives the numeric types and how a number literal gets its type. It says what the arithmetic, shift and bitwise operators do, how floats behave, how numbers convert between types and parse from strings, and how they print. [Lexical structure](02-lexical.md) gives the forms of number literals, [Types and generics](07-types.md) gives inference, and [Effects and handlers](12-effects.md) gives panics.

## Numeric types

<a id="numbers.numeric-types"></a>
The **integer types** are `i8`, `i16`, `i32`, `i64`, `u8`, `u16`, `u32` and `u64`. The **float types** are `f32` and `f64`. Together they are the **numeric types**. A signed integer type of n bits holds the integers from −2ⁿ⁻¹ to 2ⁿ⁻¹ − 1, and an unsigned one those from 0 to 2ⁿ − 1. `bool` is not a numeric type.

Tests: [numerics/bool_is_not_numeric.lt](../conformance/numerics/bool_is_not_numeric.lt), [numerics/numeric_types.lt](../conformance/numerics/numeric_types.lt).

<a id="numbers.lengths-are-i64"></a>
Lengths, indices and counts are `i64`. There is no `usize`.

Tests: [numerics/index_of_type_i32.lt](../conformance/numerics/index_of_type_i32.lt), [numerics/lengths_and_indices.lt](../conformance/numerics/lengths_and_indices.lt), [numerics/lengths_are_i64.lt](../conformance/numerics/lengths_are_i64.lt).

## Literals

<a id="numbers.integer-literals"></a>
An integer literal ([lexical.integer-literals](02-lexical.md#lexical.integer-literals)) takes the numeric type its context expects, a float type included, so `let x: f64 = 1` is valid. A literal that doesn't fit its type is E0320, *literal out of range*. An integer literal used as a float fits only if the float type represents it exactly, so `9007199254740993` can't be an `f64`.

Tests: [expressions/expected_types_accepted.lt](../conformance/expressions/expected_types_accepted.lt), [expressions/range_bound_out_of_range.lt](../conformance/expressions/range_bound_out_of_range.lt), [numerics/bool_is_not_numeric.lt](../conformance/numerics/bool_is_not_numeric.lt), [numerics/comparisons.lt](../conformance/numerics/comparisons.lt), [numerics/integer_arithmetic.lt](../conformance/numerics/integer_arithmetic.lt), [numerics/literal_defaults_rejected.lt](../conformance/numerics/literal_defaults_rejected.lt), [numerics/literal_ranges.lt](../conformance/numerics/literal_ranges.lt), [numerics/literal_typing.lt](../conformance/numerics/literal_typing.lt), [numerics/numeric_types.lt](../conformance/numerics/numeric_types.lt), [program/print_integer.lt](../conformance/program/print_integer.lt), [types/literal_ranges.lt](../conformance/types/literal_ranges.lt), [types/operator_open_left.lt](../conformance/types/operator_open_left.lt), [types/operator_open_left_undefined.lt](../conformance/types/operator_open_left_undefined.lt).

<a id="numbers.float-literals"></a>
A float literal ([lexical.float-literals](02-lexical.md#lexical.float-literals)) takes the float type its context expects. It fits its type when it rounds to a finite value of that type, so `1e39` can't be an `f32` (E0320). A float literal can't take an integer type: where one is expected, the literal is a type mismatch (E0311).

Tests: [numerics/bool_is_not_numeric.lt](../conformance/numerics/bool_is_not_numeric.lt), [numerics/float_output.lt](../conformance/numerics/float_output.lt), [numerics/literal_ranges.lt](../conformance/numerics/literal_ranges.lt), [numerics/literal_typing.lt](../conformance/numerics/literal_typing.lt), [types/literal_ranges.lt](../conformance/types/literal_ranges.lt).

<a id="numbers.literal-defaults"></a>
A literal's type is inferred from its whole body ([types.inferred-per-body](07-types.md#types.inferred-per-body)). A literal whose type is still open at the end of its body becomes an `i64`, or an `f64` for a float literal. A method call needs the receiver's type ([traits.method-resolution](11-traits.md#traits.method-resolution)). So a literal whose type is still open where a method is called on it takes its default type there. In `var total = 0` followed by `total += price` with `price: f64`, the literal `0` is an `f64`. `let x = 5` followed by `x.abs()` makes `x` an `i64`. Interpolation calls no method of the literal, so `"{x}"` leaves the type of a literal `x` open.

Tests: [expressions/known_types_in_order.lt](../conformance/expressions/known_types_in_order.lt), [numerics/conversions.lt](../conformance/numerics/conversions.lt), [numerics/literal_defaults.lt](../conformance/numerics/literal_defaults.lt), [numerics/literal_defaults_rejected.lt](../conformance/numerics/literal_defaults_rejected.lt), [numerics/shift_amount_edges.lt](../conformance/numerics/shift_amount_edges.lt), [numerics/shift_amount_not_integer.lt](../conformance/numerics/shift_amount_not_integer.lt), [numerics/shift_amounts.lt](../conformance/numerics/shift_amounts.lt), [std/format_spec_defaulted_type.lt](../conformance/std/format_spec_defaulted_type.lt), [std/format_spec_settled_type.lt](../conformance/std/format_spec_settled_type.lt), [types/undecided_type.lt](../conformance/types/undecided_type.lt), [types/unknown_receiver.lt](../conformance/types/unknown_receiver.lt).

<a id="numbers.negative-literals"></a>
In an expression, a `-` written directly before a literal, with nothing between them, counts as part of the literal when its range is checked. This holds only when the literal is the whole operand of the `-`. So `let x: i8 = -128` is valid. In `-9223372036854775808.abs()`, the operand is a method call, so the literal is checked alone, and it is out of range (E0320). Any other `-` negates its operand, so `-(128)` and `- 128` negate an `i8` that doesn't fit. In a pattern, where nothing is negated, a `-` before an integer literal is always part of it ([patterns.pattern-forms](09-patterns.md#patterns.pattern-forms)). Used as a float, a negative literal is its literal negated: `-0` is `-0.0`, as the literal `-0.0` is.

Tests: [numerics/float_output.lt](../conformance/numerics/float_output.lt), [numerics/literal_ranges.lt](../conformance/numerics/literal_ranges.lt), [numerics/literal_typing.lt](../conformance/numerics/literal_typing.lt), [numerics/negative_literal_receiver.lt](../conformance/numerics/negative_literal_receiver.lt), [numerics/negative_literals.lt](../conformance/numerics/negative_literals.lt), [numerics/negative_literals_rejected.lt](../conformance/numerics/negative_literals_rejected.lt), [numerics/negative_minimum_literal.lt](../conformance/numerics/negative_minimum_literal.lt), [numerics/negative_zero_literal.lt](../conformance/numerics/negative_zero_literal.lt), [numerics/numeric_types.lt](../conformance/numerics/numeric_types.lt), [procedural/negative_splices](../conformance/procedural/negative_splices/), [types/literal_ranges.lt](../conformance/types/literal_ranges.lt), [types/unsigned_negation.lt](../conformance/types/unsigned_negation.lt).

## Arithmetic

<a id="numbers.no-implicit-conversions"></a>
The two operands of an arithmetic or bitwise operator must have the same type, and nothing converts either one implicitly. Shifts are the exception ([numbers.shifts](#numbers.shifts)). So `i64 * f64` is E0311, *mismatched types*, whose fix converts one operand with `.to_f64()` ([numbers.conversions](#numbers.conversions)). [expressions.right-operand](08-expressions.md#expressions.right-operand) says at which operand the mismatch is reported.

Tests: [expressions/string_plus.lt](../conformance/expressions/string_plus.lt), [numerics/explicit_conversions.lt](../conformance/numerics/explicit_conversions.lt), [numerics/mixed_operands.lt](../conformance/numerics/mixed_operands.lt), [ported/caesar.lt](../conformance/ported/caesar.lt), [types/operator_mismatch_on_two_lines.lt](../conformance/types/operator_mismatch_on_two_lines.lt), [types/operator_right_mismatch.lt](../conformance/types/operator_right_mismatch.lt), [types/operator_undefined_on_left.lt](../conformance/types/operator_undefined_on_left.lt), [types/operators.lt](../conformance/types/operators.lt).

<a id="numbers.integer-panics"></a>
Integer `+`, `-` and `*` panic with the kind `overflow` when the result is out of range of their type, in every build. So do unary `-` on the minimum value of a type, `MIN / -1` and `MIN % -1`. Integer division or remainder by zero panics with the kind `divide-by-zero` ([effects.panic-kinds](12-effects.md#effects.panic-kinds)).

Tests: [declarations/constant_in_loop.lt](../conformance/declarations/constant_in_loop.lt), [declarations/constant_overflow.lt](../conformance/declarations/constant_overflow.lt), [effects/panic_divide_by_zero.lt](../conformance/effects/panic_divide_by_zero.lt), [effects/panic_overflow.lt](../conformance/effects/panic_overflow.lt), [numerics/arithmetic_edges.lt](../conformance/numerics/arithmetic_edges.lt), [numerics/divide_by_literal_zero.lt](../conformance/numerics/divide_by_literal_zero.lt), [numerics/divide_by_zero.lt](../conformance/numerics/divide_by_zero.lt), [numerics/min_divided_by_minus_one.lt](../conformance/numerics/min_divided_by_minus_one.lt), [numerics/min_remainder_minus_one.lt](../conformance/numerics/min_remainder_minus_one.lt), [numerics/multiplication_overflow.lt](../conformance/numerics/multiplication_overflow.lt), [numerics/negating_the_minimum.lt](../conformance/numerics/negating_the_minimum.lt), [numerics/overflow.lt](../conformance/numerics/overflow.lt), [numerics/remainder_by_zero.lt](../conformance/numerics/remainder_by_zero.lt), [numerics/signed_overflow_edges.lt](../conformance/numerics/signed_overflow_edges.lt), [numerics/subtracting_a_large_unsigned_constant.lt](../conformance/numerics/subtracting_a_large_unsigned_constant.lt), [numerics/subtraction_overflow.lt](../conformance/numerics/subtraction_overflow.lt), [numerics/unsigned_overflow_edges.lt](../conformance/numerics/unsigned_overflow_edges.lt), [ported/fibonacci.lt](../conformance/ported/fibonacci.lt), [program/panic_location_in_interpolation.lt](../conformance/program/panic_location_in_interpolation.lt), [std/abs_of_minimum.lt](../conformance/std/abs_of_minimum.lt).

<a id="numbers.division-and-remainder"></a>
Integer `/` truncates toward zero. The result of `%` has the sign of the dividend.

Tests: [numerics/division_signs.lt](../conformance/numerics/division_signs.lt), [numerics/integer_arithmetic.lt](../conformance/numerics/integer_arithmetic.lt), [ported/gcd.lt](../conformance/ported/gcd.lt), [ported/happy_numbers.lt](../conformance/ported/happy_numbers.lt), [ported/perfect_numbers.lt](../conformance/ported/perfect_numbers.lt).

<a id="numbers.wrapping"></a>
`+%`, `-%` and `*%`, and their compound-assignment forms `+%=`, `-%=` and `*%=`, wrap in two's complement. They are defined only on integers. On any other type, they are E0317, *operator not defined on a type*.

Tests: [expressions/compound_assignment_forms.lt](../conformance/expressions/compound_assignment_forms.lt), [numerics/bitwise_rejected.lt](../conformance/numerics/bitwise_rejected.lt), [numerics/integer_arithmetic.lt](../conformance/numerics/integer_arithmetic.lt), [numerics/literal_defaults.lt](../conformance/numerics/literal_defaults.lt), [numerics/wrapping.lt](../conformance/numerics/wrapping.lt), [ported/n_queens.lt](../conformance/ported/n_queens.lt), [types/operator_open_left_undefined.lt](../conformance/types/operator_open_left_undefined.lt), [types/operators.lt](../conformance/types/operators.lt).

<a id="numbers.shifts"></a>
`<<` and `>>` take two integer operands, which may have different types. The left operand is shifted, and the result has its type. The right operand is the amount. `>>` is arithmetic on signed types and logical on unsigned types. `<<` discards the bits it shifts out on the left, without a panic. A shift whose left operand isn't an integer is E0317.

Tests: [expressions/compound_assignment_forms.lt](../conformance/expressions/compound_assignment_forms.lt), [numerics/bitwise_rejected.lt](../conformance/numerics/bitwise_rejected.lt), [numerics/integer_arithmetic.lt](../conformance/numerics/integer_arithmetic.lt), [numerics/mixed_operands.lt](../conformance/numerics/mixed_operands.lt), [numerics/shift_edges.lt](../conformance/numerics/shift_edges.lt), [numerics/shift_mixed_types.lt](../conformance/numerics/shift_mixed_types.lt), [numerics/shifts.lt](../conformance/numerics/shifts.lt), [ported/ethiopian_multiplication.lt](../conformance/ported/ethiopian_multiplication.lt), [ported/n_queens.lt](../conformance/ported/n_queens.lt).

<a id="numbers.shift-amounts"></a>
A negative shift amount, or one at least as large as the bit width of the left operand's type, panics with the kind `overflow`, whatever the amount's own type. The amount is checked with no expected type. Its type must be an integer type: a known type that isn't one is a type mismatch at the amount (E0311). An open literal amount takes its default type, `i64`, unless something else in its body decides it ([numbers.literal-defaults](#numbers.literal-defaults)). A compound `<<=` or `>>=` checks its value in the same way, as the amount its place is shifted by.

Tests: [numerics/negative_shift.lt](../conformance/numerics/negative_shift.lt), [numerics/shift_amount_edges.lt](../conformance/numerics/shift_amount_edges.lt), [numerics/shift_amount_not_integer.lt](../conformance/numerics/shift_amount_not_integer.lt), [numerics/shift_amounts.lt](../conformance/numerics/shift_amounts.lt), [numerics/shift_by_width.lt](../conformance/numerics/shift_by_width.lt), [numerics/shift_mixed_types.lt](../conformance/numerics/shift_mixed_types.lt), [numerics/unsigned_shift_by_width.lt](../conformance/numerics/unsigned_shift_by_width.lt).

<a id="numbers.bitwise-operators"></a>
On integers, `&`, `|`, `^` and `!` operate bit by bit. On `bool`, `!` is logical not, and `&`, `|` and `^` are not defined (E0317): the logical operators are `&&`, `||` and `!=`. None of the four is defined on a float (E0317).

Tests: [numerics/bitwise.lt](../conformance/numerics/bitwise.lt), [numerics/bitwise_rejected.lt](../conformance/numerics/bitwise_rejected.lt), [numerics/integer_arithmetic.lt](../conformance/numerics/integer_arithmetic.lt), [ported/n_queens.lt](../conformance/ported/n_queens.lt), [types/operators.lt](../conformance/types/operators.lt).

<a id="numbers.unsigned-negation"></a>
Unary `-` on a value of an unsigned type is an error (E0317), unless it is part of a literal ([numbers.negative-literals](#numbers.negative-literals)). So `-0` is a valid `u8`, while `- 0` and `-(0)` are errors.

Tests: [numerics/negative_literals.lt](../conformance/numerics/negative_literals.lt), [numerics/negative_literals_rejected.lt](../conformance/numerics/negative_literals_rejected.lt), [types/operators.lt](../conformance/types/operators.lt), [types/unsigned_negation.lt](../conformance/types/unsigned_negation.lt).

<a id="numbers.comparisons"></a>
`==`, `!=`, `<`, `<=`, `>` and `>=` require both operands to have the same type (E0311).

Tests: [numerics/comparisons.lt](../conformance/numerics/comparisons.lt), [numerics/mixed_operands.lt](../conformance/numerics/mixed_operands.lt).

## Floats

<a id="numbers.ieee-754"></a>
Floats are IEEE 754 binary32 (`f32`) and binary64 (`f64`), rounded to nearest with ties to even. Every `f32` operation rounds its result to binary32. Float operations never trap: division by zero gives an infinity or NaN. On floats, `%` is `fmod`, which truncates. `==` and `<` follow IEEE, so NaN is unequal to everything, itself included.

Tests: [builds/unfused_multiply_add.lt](../conformance/builds/unfused_multiply_add.lt), [numerics/comparisons.lt](../conformance/numerics/comparisons.lt), [numerics/division_signs.lt](../conformance/numerics/division_signs.lt), [numerics/f32_printing.lt](../conformance/numerics/f32_printing.lt), [numerics/float_arithmetic.lt](../conformance/numerics/float_arithmetic.lt), [numerics/float_output.lt](../conformance/numerics/float_output.lt), [numerics/literal_defaults.lt](../conformance/numerics/literal_defaults.lt), [numerics/literal_typing.lt](../conformance/numerics/literal_typing.lt), [std/float_operations.lt](../conformance/std/float_operations.lt), [traits/float_order.lt](../conformance/traits/float_order.lt).

## Conversions

<a id="numbers.conversions"></a>
Conversions between numeric types are methods named `.to_T()`, one for each numeric type `T`, with these results:

| Conversion | Result |
| --- | --- |
| Integer to integer, where every value of the source type fits in `T` | `T` |
| Integer to integer, where some value of the source type doesn't fit in `T` | `Option<T>`, which is `None` if the value doesn't fit |
| Integer to float | `T`, rounded to nearest with ties to even |
| Float to integer | `Option<T>`: the value truncated toward zero, or `None` for NaN, the infinities and values whose truncation is out of range, so `(-0.5).to_u8()` is `Some(0)` |
| `f64` to `f32` | `f32`, rounded to nearest with ties to even; a value whose magnitude rounds beyond the largest finite `f32` becomes an infinity |
| `f32` to `f64` | `f64`, exact |
| A float to its own type | `T`, unchanged |

So `u8.to_i64()` returns an `i64`, while `i64.to_u8()` and `u64.to_i64()` return an `Option`. A `bool` has none of these methods, so `b.to_i64()` is E0314, *no such method or member*.

Tests: [numerics/conversion_types.lt](../conformance/numerics/conversion_types.lt), [numerics/conversions.lt](../conformance/numerics/conversions.lt), [numerics/explicit_conversions.lt](../conformance/numerics/explicit_conversions.lt), [numerics/f32_printing.lt](../conformance/numerics/f32_printing.lt), [numerics/float_conversions.lt](../conformance/numerics/float_conversions.lt), [numerics/integer_conversions.lt](../conformance/numerics/integer_conversions.lt), [ported/caesar.lt](../conformance/ported/caesar.lt), [procedural/numbers](../conformance/procedural/numbers/).

<a id="numbers.wrapping-conversions"></a>
For every integer type `T`, an integer's `.wrap_to_T()` keeps the low bits of its value, in two's complement. A float has no wrapping conversion (E0314).

Tests: [numerics/conversion_types.lt](../conformance/numerics/conversion_types.lt), [numerics/conversions.lt](../conformance/numerics/conversions.lt), [numerics/integer_arithmetic.lt](../conformance/numerics/integer_arithmetic.lt), [numerics/wrapping_conversions.lt](../conformance/numerics/wrapping_conversions.lt), [procedural/numbers](../conformance/procedural/numbers/).

<a id="numbers.parsing"></a>
`str.to_T()`, for each numeric type `T`, returns an `Option<T>`, which is `None` unless the whole string matches the grammar for `T` and the value is in range. An integer matches `-?[0-9]+`, where the `-` is accepted only for a signed type. Leading zeros are accepted, so `"007"` parses as 7. A float matches `-?[0-9]+(\.[0-9]+)?([eE][+-]?[0-9]+)?`, and its value is rounded to nearest with ties to even. A value whose magnitude rounds beyond the largest finite value of `T` gives `None`. Everything outside these grammars is rejected, including `+`, `_`, whitespace, radix prefixes, `1.`, `.5`, `inf` and `nan`.

Tests: [numerics/conversions.lt](../conformance/numerics/conversions.lt), [numerics/parsing_floats.lt](../conformance/numerics/parsing_floats.lt), [numerics/parsing_integers.lt](../conformance/numerics/parsing_integers.lt), [ported/digital_root.lt](../conformance/ported/digital_root.lt), [ported/luhn.lt](../conformance/ported/luhn.lt), [ported/run_length.lt](../conformance/ported/run_length.lt), [std/no_panics.lt](../conformance/std/no_panics.lt).

## Printing

<a id="numbers.printing-integers"></a>
An integer prints in decimal, with a leading `-` when it is negative.

Tests: [numerics/bitwise.lt](../conformance/numerics/bitwise.lt), [numerics/integer_arithmetic.lt](../conformance/numerics/integer_arithmetic.lt), [numerics/integer_conversions.lt](../conformance/numerics/integer_conversions.lt), [numerics/negative_literals.lt](../conformance/numerics/negative_literals.lt), [numerics/numeric_types.lt](../conformance/numerics/numeric_types.lt), [numerics/shifts.lt](../conformance/numerics/shifts.lt), [numerics/wrapping.lt](../conformance/numerics/wrapping.lt), [numerics/wrapping_conversions.lt](../conformance/numerics/wrapping_conversions.lt), [std/integer_methods.lt](../conformance/std/integer_methods.lt), [std/show_every_type.lt](../conformance/std/show_every_type.lt).

<a id="numbers.printing-floats"></a>
A float prints in the shortest form that reads back as the same value. NaN, whatever its sign and payload, prints as `nan`, the infinities as `inf` and `-inf`, and the zeros as `0.0` and `-0.0`. A negative value prints as `-` followed by the printed form of its magnitude, which [numbers.float-digits](#numbers.float-digits) and [numbers.float-notation](#numbers.float-notation) describe.

Tests: [numerics/conversions.lt](../conformance/numerics/conversions.lt), [numerics/f32_printing.lt](../conformance/numerics/f32_printing.lt), [numerics/float_arithmetic.lt](../conformance/numerics/float_arithmetic.lt), [numerics/float_conversions.lt](../conformance/numerics/float_conversions.lt), [numerics/float_output.lt](../conformance/numerics/float_output.lt), [numerics/integer_conversions.lt](../conformance/numerics/integer_conversions.lt), [numerics/literal_typing.lt](../conformance/numerics/literal_typing.lt), [numerics/negative_zero_literal.lt](../conformance/numerics/negative_zero_literal.lt), [numerics/parsing_floats.lt](../conformance/numerics/parsing_floats.lt), [std/float_operations.lt](../conformance/std/float_operations.lt), [std/integer_methods.lt](../conformance/std/integer_methods.lt), [std/show_every_type.lt](../conformance/std/show_every_type.lt).

<a id="numbers.float-digits"></a>
Every other value is written as 0.d₁…dₙ × 10ᵏ. Here d₁…dₙ is the shortest digit string that rounds back to the same value in its own format, which for an `f32` is binary32. If more than one string of that length does, the one closest to the exact value is used. Of two equally close, the one whose last digit is even is used, so `1259266790452956.25` prints as `1259266790452956.2`. These are the digits that Ryū, and Steele and White's algorithm, produce.

Tests: [numerics/f32_printing.lt](../conformance/numerics/f32_printing.lt), [numerics/float_binades.lt](../conformance/numerics/float_binades.lt), [numerics/float_output.lt](../conformance/numerics/float_output.lt).

<a id="numbers.float-notation"></a>
**Fixed notation** is used when −4 < k ≤ 16. If k ≤ 0, it writes `0.`, then −k zeros, then the digits. Otherwise it writes the digits with the decimal point after the first k of them, padding with zeros before the point as needed. It then appends `.0` if no fractional digit remains. **Scientific notation** is used for every other k. It writes the first digit, then `.` and the remaining digits if there are any, then `e`, then the exponent k − 1 in decimal. The exponent has a `-` only when it is negative.

| Value | Prints as |
| --- | --- |
| `1.0` | `1.0` |
| `0.1` | `0.1` |
| `123456.789` | `123456.789` |
| `0.0001` | `0.0001` |
| `0.00001` | `1e-5` |
| `1.5e-7` | `1.5e-7` |
| `1e16` | `1e16` |

Tests: [numerics/float_output.lt](../conformance/numerics/float_output.lt), [numerics/float_thresholds.lt](../conformance/numerics/float_thresholds.lt), [std/format_scientific.lt](../conformance/std/format_scientific.lt).

<a id="numbers.format-specs"></a>
An interpolation's format spec changes this output, as `{t:.2}` prints a fixed number of decimals. [The standard library's contract](17-std.md#std.width-fill-and-alignment) defines the specs.

Tests: [std/format_precision.lt](../conformance/std/format_precision.lt), [std/format_scientific.lt](../conformance/std/format_scientific.lt), [std/format_specs.lt](../conformance/std/format_specs.lt).
