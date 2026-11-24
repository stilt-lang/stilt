# 6. Numbers: rationale

Every rule about numbers serves two aims. A program means the same thing in every build and on every implementation, so that the reference interpreter and the compiler can be compared byte for byte. And a mistake with numbers is caught where it is written, not where its result turns out wrong.

## Numeric types

Lengths, indices and counts are `i64` ([numbers.lengths-are-i64](../06-numbers.md#numbers.lengths-are-i64)). The alternative is an unsigned length type, as Rust's `usize`. Unsigned lengths invite bugs when something is subtracted from them: `xs.len() - 3` would overflow for a short list. They also need a conversion at every call site where a length meets ordinary arithmetic. Go, Java and Swift use signed lengths, and `i64` covers every real length on a 64-bit target. 32-bit targets and WebAssembly check lengths at the boundary.

`bool` isn't numeric ([numbers.numeric-types](../06-numbers.md#numbers.numeric-types)): no integer stands in for a truth value, and no truth value for an integer.

## Literals

A literal has no type of its own. It takes the one its context expects ([numbers.integer-literals](../06-numbers.md#numbers.integer-literals), [numbers.float-literals](../06-numbers.md#numbers.float-literals)), so no suffix is ever written. A literal that doesn't fit is an error, and is never rounded or truncated in silence. 2⁵³ + 1 is the first integer that an `f64` can't hold, and a program that writes it as an `f64` almost certainly means something else.

The defaults ([numbers.literal-defaults](../06-numbers.md#numbers.literal-defaults)) look at the whole body. So `var total = 0` followed by `total += price` gives the sum the type of the prices, as a reader expects. A method call is the one place where the body can't be waited for. Which method is called depends on the receiver's type ([traits.method-resolution](../11-traits.md#traits.method-resolution)), so an open literal takes its default there.

The rule on negative literals ([numbers.negative-literals](../06-numbers.md#numbers.negative-literals)) lets `-128` be an `i8`, and keeps the precedence of `-` everywhere else. It goes by what is written: a `-` directly before a literal that is its whole operand. `-9223372036854775808.abs()` negates a method call, as the precedence table says, so its literal stands alone and is out of range.

## Arithmetic

Nothing converts implicitly ([numbers.no-implicit-conversions](../06-numbers.md#numbers.no-implicit-conversions)), not even `i32` to `i64`, as in Rust and Go. A conversion is a decision about range and precision, and the error offers the method that makes it.

Integer overflow panics in every build ([numbers.integer-panics](../06-numbers.md#numbers.integer-panics)). The alternative, Rust's wrapping in release builds, gives one program two meanings, and debug and release builds must mean the same thing. Wrapping is available where it is wanted, through operators that say so ([numbers.wrapping](../06-numbers.md#numbers.wrapping)). Division truncates toward zero and the remainder takes the dividend's sign, as in C, Rust and Go.

A shift's amount has a type of its own ([numbers.shifts](../06-numbers.md#numbers.shifts)), as in Rust. The alternative, an amount of the left operand's type, fits poorly: an amount counts bits, so it is rarely a value of the shifted type. Bitboards are `u64` while squares and indexes are `i64`, so every shift would convert its amount.

On `bool`, `&`, `|` and `^` aren't defined ([numbers.bitwise-operators](../06-numbers.md#numbers.bitwise-operators)). `&&` and `||` already exist, and short-circuit, and `!=` is exclusive or. A `-` written as part of a literal is the literal's sign, and negates nothing. So `-0` stays a valid `u8`, while negating an unsigned value is an error ([numbers.unsigned-negation](../06-numbers.md#numbers.unsigned-negation)).

## Floats

Floats follow IEEE 754 with one rounding mode, and every `f32` operation rounds to binary32 ([numbers.ieee-754](../06-numbers.md#numbers.ieee-754)). So implementations compute the same bits on every target. Float operations never trap: a division by zero gives an infinity or NaN. `==` follows IEEE, so NaN is unequal to itself. The total order that sorting needs is `compare` ([traits.floats](../11-traits.md#traits.floats)).

## Conversions

A conversion's result type says whether it can fail ([numbers.conversions](../06-numbers.md#numbers.conversions)): `u8` to `i64` returns an `i64`, and `i64` to `u8` an `Option<u8>`. So a narrowing conversion can't be written without deciding what happens to a value that doesn't fit, and the type checker sees that decision. A conversion that keeps the low bits is a method of its own ([numbers.wrapping-conversions](../06-numbers.md#numbers.wrapping-conversions)), so wrapping is always visible.

Parsing returns an `Option` too. `str.to_T()` accepts one grammar and rejects everything else ([numbers.parsing](../06-numbers.md#numbers.parsing)): no `+`, no `_`, no whitespace, no radix prefix, no `inf` or `nan`. A strict grammar parses the same strings everywhere, and a program that needs another form says so in code.

## Printing

A float prints in the shortest form that reads back as the same value ([numbers.printing-floats](../06-numbers.md#numbers.printing-floats), [numbers.float-digits](../06-numbers.md#numbers.float-digits)), the output of Ryū and of Steele and White's algorithm. The digits must be exact, because the reference interpreter and the compiler must print the same text for their outputs to be compared.

The thresholds between fixed and scientific notation ([numbers.float-notation](../06-numbers.md#numbers.float-notation)) are close to those of Python's `repr`. The alternative of never printing an exponent, as Rust's `Display` does, makes very large and very small values unreadable.

Printing exactly has a cost for an implementation. A printer that tries `%.{p}e` with increasing `p` finds the shortest length. At binade boundaries, though, the closest candidate of that length can fail to read back while one of its neighbours succeeds, so both neighbours have to be tried. Such a printer relies on the C library converting between binary and decimal exactly, as glibc and the macOS library do. The reference interpreter's own tests cover these cases.
