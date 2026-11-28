# 17. The standard library

This chapter is the contract of the standard library: what each module and type guarantees, which effects its functions perform, and where they panic. The signature of each function, and an example of it, are in the library's sources, `std/`, which every implementation reads. [Numbers](06-numbers.md) gives arithmetic, conversions and printing. [Traits](11-traits.md) gives the prelude traits and the structural impls, and [Effects and handlers](12-effects.md) gives raising and panics.

## Modules

<a id="std.modules"></a>
The standard library is these modules:

| Module | What it holds |
| --- | --- |
| `std.prelude` | `Option`, `Result`, `Ordering` and `Set`, the traits `Eq`, `Ord`, `Hash` and `Show`, the prelude functions, and the methods of the built-in types; it is in scope in every module ([program.contents](04-programs.md#program.contents)) |
| `std.io` | Standard input and output, and `IoError` ([std.io](#std.io)) |
| `std.fs` | Files, their bytes, directories and paths ([std.fs](#std.fs)) |
| `std.cli` | Command-line arguments and the environment ([std.cli](#std.cli)) |
| `std.math` | The transcendental functions of `f64` ([std.math](#std.math)) |
| `std.clock` | The system's clocks and waiting, durations, instants, and dates and times in UTC ([std.clock](#std.clock), [std.durations](#std.durations)) |
| `std.process` | Other programs, run to their end or beside the program ([std.process](#std.process)) |
| `std.net` | TCP connections and listeners, UDP sockets, and the addresses of hosts ([std.net](#std.net), [std.net-datagrams](#std.net-datagrams)) |
| `std.http` | HTTP/1.1 messages, a client of `http://` URLs and a server ([std.http](#std.http)) |
| `std.random` | `Rng`, a generator that a seed reproduces ([std.random](#std.random)) |
| `std.collections` | `Deque` and `Heap` ([std.deque](#std.deque), [std.heap](#std.heap)) |
| `std.encoding` | Base64, hexadecimal and UTF-8 with its errors ([std.encoding](#std.encoding)) |
| `std.hashing` | SHA-256, its HMAC, and FNV-1a ([std.hashing](#std.hashing)) |
| `std.text` | Unicode's case mappings and properties of characters ([std.text](#std.text)) |
| `std.regex` | Regular expressions, matched in time linear in the text ([std.regex](#std.regex)) |
| `std.json` | JSON values and text, and any type written and read through its shape ([std.json](#std.json)) |
| `std.view` | Views and iterators ([views.std-view](13-modes.md#views.std-view)) |
| `std.lazy` | `Lazy`, a value computed on its first use ([polymorphism.lazy-values](07-types.md#polymorphism.lazy-values)) |
| `std.array` | `Array<T, n>`, a fixed number of values stored inline ([generics.arrays](07-types.md#generics.arrays)) |
| `std.meta` | Shapes, and the tokens and code of procedural macros ([meta.std-meta](16-meta.md#meta.std-meta), [macros.tokens-and-code](16-meta.md#macros.tokens-and-code)) |
| `std.task` | Tasks and the handlers of `async` ([tasks.std-task](14-tasks.md#tasks.std-task)) |
| `std.sync` | `Shared`, a value that tasks share ([shared.std-sync](14-tasks.md#shared.std-sync)) |
| `std.par` | Deterministic parallel functions ([par.std-par](14-tasks.md#par.std-par)) |
| `std.c` | The addresses and strings that C takes ([c.module-std-c](20-builds.md#c.module-std-c)) |

Every module but `std.prelude` is imported with `use`, and its items are written through it, as in `fs.read` ([program.what-use-binds](04-programs.md#program.what-use-binds)). None of them adds a name to the prelude. The library declares six traits: `Eq`, `Ord`, `Hash` and `Show` in the prelude ([traits.prelude-traits](11-traits.md#traits.prelude-traits)), and `ToJson` and `FromJson` in `std.json` ([std.json](#std.json)).

Checked by: the library's sources in `std/`, which every implementation reads and checks with every program it checks.

## Principles

<a id="std.natives"></a>
A function of the library is either native or written in Stilt. A **native** function's body is written `?` in the sources, and each implementation provides it ([declarations.native-items](10-declarations.md#declarations.native-items)). A function written in Stilt has its body in the sources, which every implementation shares. It behaves as its source does, including its raises, its panics and its calls of its callbacks. So `retain` whose `keep` raises leaves the list as it was. Where this chapter says less than the source, the source decides. A native behaves as this chapter says, the same in every implementation.

Tests: [std/list_callbacks.lt](../conformance/std/list_callbacks.lt), [std/retain_with_raising_keep.lt](../conformance/std/retain_with_raising_keep.lt).

<a id="std.no-panics-by-default"></a>
Where a value may be missing or an operation may fail, a function of the library returns an `Option` or raises. It panics only where this chapter says it does:

- on an index out of bounds;
- on a precondition that the function's paragraph states;
- by an operator whose panic its paragraph names ([numbers.integer-panics](06-numbers.md#numbers.integer-panics));
- in `unwrap` and `expect` ([std.option-result-and-ordering](#std.option-result-and-ordering)), which panic where a value is missing.

A function written in Stilt that panics on a precondition panics with the kind `explicit` ([effects.panic-kinds](12-effects.md#effects.panic-kinds)). Its detail is the message that its paragraph gives, quoted as [program.panic-report](04-programs.md#program.panic-report) says. So `[1, 2].chunks(0)` panics with the detail `"chunks needs a size of at least 1, not 0"`.

Tests: [std/bounds_edges.lt](../conformance/std/bounds_edges.lt), [std/list_chunks_panic.lt](../conformance/std/list_chunks_panic.lt), [std/list_index_out_of_bounds.lt](../conformance/std/list_index_out_of_bounds.lt), [std/list_windows_panic.lt](../conformance/std/list_windows_panic.lt), [std/no_panics.lt](../conformance/std/no_panics.lt), [std/random_below_panic.lt](../conformance/std/random_below_panic.lt), [std/random_range_panic.lt](../conformance/std/random_range_panic.lt).

<a id="std.callbacks"></a>
A function that takes a callback calls it once per element, from the first element to the last, unless its paragraph says otherwise. `any`, `all`, `find`, `find_index`, `take_while` and `skip_while` stop at the first element that decides the result. `reduce` calls its callback once per element after the first. `sorted_by`, `sorted_desc_by`, `sort_by` and `sort_desc_by` call `key` once per element, in order, before they sort. How often and in which order they compare the keys is unspecified. Every callback is a non-escaping parameter, so its effects pass through to the caller ([effects.non-escaping-parameters](12-effects.md#effects.non-escaping-parameters)).

Tests: [std/callback_order.lt](../conformance/std/callback_order.lt), [std/callbacks.lt](../conformance/std/callbacks.lt), [std/list_callbacks.lt](../conformance/std/list_callbacks.lt).

<a id="std.method-names"></a>
A method of the library named by a verb changes its receiver, which it takes `inout`, as `push`, `sort` and `reverse` do. It returns `()`, unless what it takes out is its result, as with `pop`. A method named by a past participle returns a new value and leaves its receiver as it was, as `sorted`, `reversed`, `deduped` and `merged` do. When a method has both forms, they share one stem, and the verb replaces the receiver with what the participle returns. Terms of art keep the names that other languages give them, though they return new values, as `map`, `filter`, `fold`, `zip`, `take`, `skip` and `concat` do, or though they change their receiver and return a value, as `Map.get_or_insert(k, d)` does. A generator's state isn't the receiver this rule speaks of: `Rng.shuffled(xs)` advances the generator it takes `inout` and leaves `xs` as it was, as a participle does. So does every method of `str`: no method changes a string ([values.strings](05-values.md#values.strings)). So `xs.sort()` sorts a `var`, and `xs.sorted()` alone on a line is an unused value ([expressions.unused-values](08-expressions.md#expressions.unused-values)).

Tests: [std/participles_copy.lt](../conformance/std/participles_copy.lt), [std/sort_in_place.lt](../conformance/std/sort_in_place.lt), [std/sort_through_inout.lt](../conformance/std/sort_through_inout.lt).

## Numbers

<a id="std.integers"></a>
Every integer type `T` has the native constants `T.MIN` and `T.MAX`, the conversions of [numbers.conversions](06-numbers.md#numbers.conversions) and [numbers.wrapping-conversions](06-numbers.md#numbers.wrapping-conversions), and these native methods, whose results are exact:

| Method | Result |
| --- | --- |
| `abs(self) -> T` | The absolute value; panics with `overflow` for `T.MIN` of a signed type |
| `min(self, other: T) -> T`, `max(self, other: T) -> T` | The smaller and the larger of the two |
| `checked_add(self, other: T) -> Option<T>`, `checked_sub`, `checked_mul` | `Some` of the exact result when it fits in `T`, and `None` otherwise |
| `saturating_add(self, other: T) -> T`, `saturating_sub` | The exact result, clamped to `T.MIN ..= T.MAX` |
| `pow(self, exp: u32) -> T` | `self` to the power `exp`, with `x.pow(0) == 1` for every `x`, 0 included; panics with `overflow` when the exact result doesn't fit, whatever order an implementation multiplies in, so `(-2).pow(63)` is `i64.MIN` |
| `div_euclid(self, other: T) -> T`, `rem_euclid(self, other: T) -> T` | The quotient `q` and the remainder `r` of Euclidean division, with `self == q * other + r` and `0 <= r < \|other\|`; each panics with `divide-by-zero` when `other` is 0, and with `overflow` for `T.MIN` by `-1` |
| `count_ones(self) -> i64`, `leading_zeros(self) -> i64`, `trailing_zeros(self) -> i64` | Counts of `self`'s bits in two's complement at `T`'s width; the leading and the trailing zeros of 0 are the width |
| `gcd(self, other: T) -> T`, `lcm(self, other: T) -> T` | The greatest common divisor and the least common multiple of `\|self\|` and `\|other\|`, never negative, with `0.gcd(0) == 0` and an `lcm` of 0 when either is 0; each panics with `overflow` when its result doesn't fit in `T`, as `T.MIN.gcd(0)`'s doesn't |

A call of `abs`, `pow`, `gcd` or `lcm` adds the implicit effect `overflow`. A call of `div_euclid` or `rem_euclid` adds `panic` unless its divisor is written as an integer literal other than zero. It adds `overflow` unless its divisor is written as an integer literal other than `0` and `-1` ([effects.overflow-effect](12-effects.md#effects.overflow-effect), [effects.panicking-operations](12-effects.md#effects.panicking-operations)).

Tests: [numerics/arithmetic_edges.lt](../conformance/numerics/arithmetic_edges.lt), [numerics/integer_arithmetic.lt](../conformance/numerics/integer_arithmetic.lt), [numerics/numeric_types.lt](../conformance/numerics/numeric_types.lt), [numerics/signed_overflow_edges.lt](../conformance/numerics/signed_overflow_edges.lt), [numerics/unsigned_overflow_edges.lt](../conformance/numerics/unsigned_overflow_edges.lt), [ported/fibonacci.lt](../conformance/ported/fibonacci.lt), [ported/gcd.lt](../conformance/ported/gcd.lt), [ported/levenshtein.lt](../conformance/ported/levenshtein.lt), [procedural/numbers](../conformance/procedural/numbers/), [std/abs_of_minimum.lt](../conformance/std/abs_of_minimum.lt), [std/euclid_without_panic.lt](../conformance/std/euclid_without_panic.lt), [std/integer_bits.lt](../conformance/std/integer_bits.lt), [std/integer_checked_saturating.lt](../conformance/std/integer_checked_saturating.lt), [std/integer_euclid.lt](../conformance/std/integer_euclid.lt), [std/integer_euclid_by_zero.lt](../conformance/std/integer_euclid_by_zero.lt), [std/integer_euclid_min.lt](../conformance/std/integer_euclid_min.lt), [std/integer_gcd_lcm.lt](../conformance/std/integer_gcd_lcm.lt), [std/integer_gcd_min.lt](../conformance/std/integer_gcd_min.lt), [std/integer_lcm_overflow.lt](../conformance/std/integer_lcm_overflow.lt), [std/integer_methods.lt](../conformance/std/integer_methods.lt), [std/integer_pow.lt](../conformance/std/integer_pow.lt), [std/integer_pow_overflow.lt](../conformance/std/integer_pow_overflow.lt).

<a id="std.floats"></a>
`f32` and `f64` have these constants:

- natively, `T.PI` and `T.E`, the values closest to π and e, and `T.NAN` and `T.INFINITY`;
- written in Stilt, `T.MAX` and `T.MIN`, the largest and the smallest finite values (`±1.7976931348623157e308` for `f64`, `±3.4028235e38` for `f32`);
- written in Stilt, `T.EPSILON`, the difference between 1.0 and the next larger value (`2.220446049250313e-16` and `1.1920929e-7`);
- written in Stilt, `T.MIN_POSITIVE`, the smallest positive normal value (`2.2250738585072014e-308` and `1.1754944e-38`).

Their native methods are the operations that IEEE 754 defines exactly, so every implementation computes the same bits:

- `sqrt`, `floor`, `ceil`, `trunc`, `abs`, and `round`, which rounds halves away from zero, each taking `self` and returning `T`;
- `min` and `max`, which take a second operand and are IEEE 754-2019 `minimum` and `maximum`, so a NaN operand gives NaN and `-0.0` is less than `0.0`;
- `is_nan`.

Written in Stilt, `is_finite` is whether `self` is neither infinite nor NaN, and `is_infinite` whether it is an infinity. Their conversions are those of [numbers.conversions](06-numbers.md#numbers.conversions), and the transcendental functions are in `std.math` ([std.math](#std.math)).

Tests: [numerics/f32_printing.lt](../conformance/numerics/f32_printing.lt), [numerics/float_output.lt](../conformance/numerics/float_output.lt), [procedural/numbers](../conformance/procedural/numbers/), [std/float_operations.lt](../conformance/std/float_operations.lt), [std/numbers_in_stilt.lt](../conformance/std/numbers_in_stilt.lt), [std/transcendentals_rejected.lt](../conformance/std/transcendentals_rejected.lt).

<a id="std.clamp-and-sum"></a>
Every numeric type `T` has two functions written in Stilt:

- `clamp(self, lo: T, hi: T) -> T`, which is `self.max(lo).min(hi)`, so a NaN stays NaN, a NaN bound gives NaN too, and `hi` wins when `lo > hi`;
- `T.sum(xs: List<T>) -> T`, the elements added from the first to the last onto a zero.

For floats, that zero is `0.0`, so `f64.sum([-0.0])` is `0.0`. On integers, `sum` panics with `overflow` as `+` does. A list's sum is written `i64.sum(xs)`, since an inherent block can't be specialized to `List<i64>` ([traits.impl-blocks](11-traits.md#traits.impl-blocks)).

Tests: [ported/digital_root.lt](../conformance/ported/digital_root.lt), [ported/perfect_numbers.lt](../conformance/ported/perfect_numbers.lt), [std/clamp_nan_bounds.lt](../conformance/std/clamp_nan_bounds.lt), [std/numbers_in_stilt.lt](../conformance/std/numbers_in_stilt.lt), [std/sum_overflow.lt](../conformance/std/sum_overflow.lt).

<a id="std.math"></a>
`std.math` holds native functions of `f64` arguments, each returning an `f64`. They are `pow(x: f64, y: f64)`, `exp(x)`, `log(x)`, the natural logarithm, `log2(x)`, `log10(x)`, `sin(x)`, `cos(x)`, `tan(x)`, `asin(x)`, `acos(x)`, `atan(x)`, `atan2(y: f64, x: f64)`, `sinh(x)`, `cosh(x)`, `tanh(x)`, `cbrt(x)` and `hypot(x: f64, y: f64)`. They perform nothing and never panic. Their results are specified within a tolerance, not bit for bit. When the exact value is finite and no larger in magnitude than `f64.MAX`, the result is finite and within 4 ulps of it.

Tests: [procedural/numbers](../conformance/procedural/numbers/), [std/math.lt](../conformance/std/math.lt).

Checked by: for the tolerance, which no conformance test can compare across platforms, the examples of `std.math`, which compare their results within a margin, and the runtime's tests of the exact special values (`compiler/stilt-runtime/src/std_math.rs`).

<a id="std.math-special-values"></a>
These special values of `std.math`, and no others, are exact:

- a NaN argument gives NaN, except as the next two items say;
- `pow(x, 0.0)` and `pow(1.0, y)` are `1.0` for every `x` and `y`, NaN included;
- `hypot` of an infinity is `inf`, even beside a NaN;
- `exp(-inf)` is `0.0` and `exp(inf)` is `inf`;
- `log`, `log2` and `log10` of `±0.0` are `-inf`, of a negative value NaN, of `inf` `inf`, and of `1.0` `0.0`;
- `sin`, `cos` and `tan` of an infinity are NaN, and `asin` and `acos` of a value beyond `±1` are NaN;
- `sin`, `tan`, `asin`, `atan`, `sinh`, `tanh` and `cbrt` of `±0.0` are that zero, with its sign;
- `cos(0.0)` and `exp(0.0)` are `1.0`.

Tests: [std/math.lt](../conformance/std/math.lt).

## Strings

<a id="std.bytes-and-scalars"></a>
String lengths and offsets count bytes. Widths count Unicode scalar values: a format spec's width ([std.width-fill-and-alignment](#std.width-fill-and-alignment)) and the widths of `pad_start` and `pad_end` ([std.str-building](#std.str-building)). The **ASCII whitespace** is space, `\t`, `\n`, `\r` and form feed. Case mapping, trimming and classifying handle ASCII only.

Tests: [std/format_alignment.lt](../conformance/std/format_alignment.lt), [std/format_specs.lt](../conformance/std/format_specs.lt), [std/slice_inside_a_character.lt](../conformance/std/slice_inside_a_character.lt), [std/slice_starting_inside_a_character.lt](../conformance/std/slice_starting_inside_a_character.lt), [std/string_edges.lt](../conformance/std/string_edges.lt), [std/strings.lt](../conformance/std/strings.lt).

<a id="std.str"></a>
Every method of `str` is native except `repeat` and `eq_ignore_ascii_case`. Every function of `str` is native except `str.from_code_points`. None of them changes a string. None panics except `slice`, and `with_c_str`, which lends C a copy of the string ([c.lending-buffer](20-builds.md#c.lending-buffer)). `slice(start, end)` gives the bytes from `start` up to `end`. It panics with `bounds` unless `0 ≤ start ≤ end ≤ len`, and otherwise with `utf8-boundary` when an offset falls inside a UTF-8 sequence. So `"é".slice(1, 0)` panics with `bounds`. `len()` is the length in bytes, `is_empty()` whether the string is `""`, `chars()` one string per scalar value, `char_count()` the number of scalar values, and `bytes()` the raw bytes. `s.to_T()` parses a number of each numeric type `T` ([numbers.parsing](06-numbers.md#numbers.parsing)). Indexing a string is E0317, *operator not defined on a type* ([expressions.indexing](08-expressions.md#expressions.indexing)).

Tests: [effects/panic_utf8_boundary.lt](../conformance/effects/panic_utf8_boundary.lt), [lexical/one_character_strings.lt](../conformance/lexical/one_character_strings.lt), [numerics/lengths_and_indices.lt](../conformance/numerics/lengths_and_indices.lt), [numerics/lengths_are_i64.lt](../conformance/numerics/lengths_are_i64.lt), [numerics/parsing_floats.lt](../conformance/numerics/parsing_floats.lt), [numerics/parsing_integers.lt](../conformance/numerics/parsing_integers.lt), [ported/digital_root.lt](../conformance/ported/digital_root.lt), [ported/look_and_say.lt](../conformance/ported/look_and_say.lt), [ported/luhn.lt](../conformance/ported/luhn.lt), [std/bounds_edges.lt](../conformance/std/bounds_edges.lt), [std/no_panics.lt](../conformance/std/no_panics.lt), [std/slice_bounds_before_boundaries.lt](../conformance/std/slice_bounds_before_boundaries.lt), [std/slice_inside_a_character.lt](../conformance/std/slice_inside_a_character.lt), [std/slice_starting_inside_a_character.lt](../conformance/std/slice_starting_inside_a_character.lt), [std/string_index.lt](../conformance/std/string_index.lt), [std/string_slice_out_of_bounds.lt](../conformance/std/string_slice_out_of_bounds.lt), [std/strings.lt](../conformance/std/strings.lt).

<a id="std.str-search"></a>
`contains(sub)`, `starts_with(prefix)` and `ends_with(suffix)` test for a substring, and every string contains `""`. `find(sub)` and `rfind(sub)` give the byte offset of the first and of the last occurrence. The last occurrence may overlap earlier ones, so `"aaa".rfind("aa")` is `Some(1)`. `find("")` is `Some(0)` and `rfind("")` is `Some(len)`. `count(sub)` counts the non-overlapping occurrences from left to right, and `count("")` is the number of scalar values plus one. `split_once(sep)` and `rsplit_once(sep)` give the text before and after the occurrence that `find` and `rfind` find, or `None`. So `split_once("")` is `Some(("", s))` and `rsplit_once("")` is `Some((s, ""))`. `strip_prefix(prefix)` and `strip_suffix(suffix)` give the rest of the string when it starts or ends with their argument, and `None` otherwise.

Tests: [std/string_edges.lt](../conformance/std/string_edges.lt), [std/string_natives.lt](../conformance/std/string_natives.lt), [std/strings.lt](../conformance/std/strings.lt).

<a id="std.str-splitting"></a>
`split(sep)` gives the pieces between the occurrences of `sep`. So `"a,,b".split(",")` is `["a", "", "b"]` and `"".split(",")` is `[""]`. An empty `sep` splits into scalar values, as `chars` does. `lines()` splits on `\n`, strips one trailing `\r` from each line, and gives no empty last line after a final newline, so `"".lines()` is `[]`. `split_whitespace()` gives the pieces between runs of ASCII whitespace ([std.str-classes](#std.str-classes)), none of them empty, so `" a  b ".split_whitespace()` is `["a", "b"]`. `trim()` strips ASCII whitespace from both ends, and `trim_start()` and `trim_end()` from one.

Tests: [std/read_files/main.lt](../conformance/std/read_files/main.lt), [std/string_edges.lt](../conformance/std/string_edges.lt), [std/string_natives.lt](../conformance/std/string_natives.lt), [std/strings.lt](../conformance/std/strings.lt).

<a id="std.str-building"></a>
`replace(from, to)` replaces every non-overlapping occurrence, from left to right. An empty `from` inserts `to` at every boundary between scalar values, both ends included, so `"ab".replace("", "-")` is `"-a-b-"` and `"".replace("", "-")` is `"-"`. `replace_first(from, to)` replaces the first occurrence only, and an empty `from` inserts `to` at the start. `sep.join(parts)` joins `parts` with `sep` between them. `repeat(n)` gives `n` copies of the string, and `""` when `n <= 0`. `reversed()` gives the scalar values in reverse order. `pad_start(width, fill)` and `pad_end(width, fill)` add copies of `fill` before or after the string until it holds `width` scalar values, the last copy cut short at its end. So `"7".pad_start(4, "ab")` is `"aba7"`. A string already that wide, or an empty `fill`, comes back unchanged. `ascii_upper()` and `ascii_lower()` change the case of ASCII letters only.

Tests: [ported/ackermann.lt](../conformance/ported/ackermann.lt), [ported/bottles.lt](../conformance/ported/bottles.lt), [ported/look_and_say.lt](../conformance/ported/look_and_say.lt), [ported/pascal.lt](../conformance/ported/pascal.lt), [ported/run_length.lt](../conformance/ported/run_length.lt), [std/participles_copy.lt](../conformance/std/participles_copy.lt), [std/string_edges.lt](../conformance/std/string_edges.lt), [std/string_natives.lt](../conformance/std/string_natives.lt), [std/strings.lt](../conformance/std/strings.lt).

<a id="std.str-classes"></a>
`is_ascii()` is whether every byte is below `0x80`, so `"".is_ascii()` is `true`. Each of these methods is whether the string isn't empty and every byte is of its class:

- `is_ascii_digit`, an ASCII digit;
- `is_ascii_alpha`, an ASCII letter;
- `is_ascii_alphanumeric`, an ASCII digit or an ASCII letter;
- `is_ascii_whitespace`, ASCII whitespace: a space, `\t`, `\n`, `\r` or a form feed, `\u{c}`, but not a vertical tab;
- `is_ascii_upper`, an uppercase ASCII letter;
- `is_ascii_lower`, a lowercase ASCII letter.

So `"7".is_ascii_digit()` classifies one character, and `"".is_ascii_digit()` is `false`. `eq_ignore_ascii_case(other)` is whether the two strings are equal once their ASCII letters are lowered.

Tests: [ported/run_length.lt](../conformance/ported/run_length.lt), [std/string_classes.lt](../conformance/std/string_classes.lt).

<a id="std.code-points"></a>
`code_points()` gives a string's scalar values as `u32`s. `str.from_code_point(p)` gives the string of one scalar value. It is `None` for a surrogate, `0xD800` to `0xDFFF`, and for a value above `0x10FFFF`. `str.from_code_points(cs)` gives the string of several, and `None` when one of them is invalid. `str.from_utf8(bytes)` gives the string whose bytes these are, and `None` unless they are valid UTF-8. Valid UTF-8 rules out overlong forms, surrogates and values above `0x10FFFF`. `str.from_utf8_lossy(bytes)` replaces each maximal subpart of an invalid sequence with one U+FFFD, as the Unicode Standard recommends (§3.9). Every function of the library that reads text from outside the program does the same.

Tests: [ported/caesar.lt](../conformance/ported/caesar.lt), [std/string_code_points.lt](../conformance/std/string_code_points.lt).

<a id="std.text"></a>
`std.text` is written in Stilt on tables of Unicode's data. It performs nothing and never panics. `text.unicode_version()` is the version of Unicode that the tables hold, `"17.0.0"`. `text.upper(t)` and `text.lower(t)` replace each scalar value of `t` by its full case mapping in Unicode's data. They leave out the mappings that SpecialCasing.txt makes depend on context or language. One scalar value may become several: `text.upper("straße")` is `"STRASSE"`, `text.lower("İ")` is `"i\u{307}"`, and a final `Σ` lowercases to `σ`, as every `Σ` does. Each of these functions is whether `t` isn't empty and each of its scalar values has a property of Unicode's:

- `text.is_letter(t)`, Alphabetic;
- `text.is_upper(t)`, Uppercase;
- `text.is_lower(t)`, Lowercase;
- `text.is_numeric(t)`, a general category of `N`;
- `text.is_whitespace(t)`, White_Space;
- `text.is_alphanumeric(t)`, Alphabetic or a general category of `N`.

Tests: [text/case.lt](../conformance/text/case.lt), [text/classes.lt](../conformance/text/classes.lt).

## Lists

<a id="std.lists"></a>
`List<T>` has, natively, `List.new()` and list literals, `len()`, `is_empty()` and `get(i)`. Its other natives are `xs[i]` and `xs[i] = v`, `push(x)`, `pop()`, `insert(i, x)`, `remove(i)`, `slice(start, end)`, `sorted_by` and `sorted_desc_by`. `get(i)` is `None` unless `0 ≤ i < len`. `pop()` removes and gives the last element, or `None`. `remove(i)` removes and gives element `i`. These panic with `bounds`:

- indexing and storing, unless `0 ≤ i < len`;
- `insert`, unless `0 ≤ i ≤ len`;
- `remove`, unless `0 ≤ i < len`;
- `slice`, unless `0 ≤ start ≤ end ≤ len`.

`with_ptr` and `with_mut_ptr`, which lend C a list ([c.lending-buffer](20-builds.md#c.lending-buffer)), are native too. Every other function of `List` is written in Stilt, and panics only where its paragraph says so.

Tests: [effects/panic_bounds.lt](../conformance/effects/panic_bounds.lt), [expressions/fields_through_options_key_paths.lt](../conformance/expressions/fields_through_options_key_paths.lt), [expressions/known_outer_constructor.lt](../conformance/expressions/known_outer_constructor.lt), [expressions/less_than_not_generics.lt](../conformance/expressions/less_than_not_generics.lt), [modes/e0412_fixes.lt](../conformance/modes/e0412_fixes.lt), [numerics/index_of_type_i32.lt](../conformance/numerics/index_of_type_i32.lt), [numerics/lengths_and_indices.lt](../conformance/numerics/lengths_and_indices.lt), [numerics/lengths_are_i64.lt](../conformance/numerics/lengths_are_i64.lt), [ported/balanced_brackets.lt](../conformance/ported/balanced_brackets.lt), [ported/bottles.lt](../conformance/ported/bottles.lt), [ported/hundred_doors.lt](../conformance/ported/hundred_doors.lt), [ported/levenshtein.lt](../conformance/ported/levenshtein.lt), [ported/sieve.lt](../conformance/ported/sieve.lt), [std/bounds_edges.lt](../conformance/std/bounds_edges.lt), [std/list_edges.lt](../conformance/std/list_edges.lt), [std/list_get_scalars.lt](../conformance/std/list_get_scalars.lt), [std/list_index_out_of_bounds.lt](../conformance/std/list_index_out_of_bounds.lt), [std/list_insert_out_of_bounds.lt](../conformance/std/list_insert_out_of_bounds.lt), [std/list_remove_out_of_bounds.lt](../conformance/std/list_remove_out_of_bounds.lt), [std/list_slice_out_of_bounds.lt](../conformance/std/list_slice_out_of_bounds.lt), [std/list_store_out_of_bounds.lt](../conformance/std/list_store_out_of_bounds.lt), [std/lists.lt](../conformance/std/lists.lt), [std/loops_over_pairs.lt](../conformance/std/loops_over_pairs.lt), [std/no_panics.lt](../conformance/std/no_panics.lt), [std/string_index.lt](../conformance/std/string_index.lt).

<a id="std.list-functions"></a>
A list's functions that take a callback call it as [std.callbacks](#std.callbacks) says. Among them are `map`, `filter`, `filter_map`, `flat_map`, `fold`, `scan`, `reduce`, `any`, `all`, `find`, `find_index`, `count`, `partition`, `group_by`, `count_by`, `min_by`, `max_by` and `retain`. `filter_map` gives the values of the `Some`s its callback returns, in order. `scan(init, f)` gives `init` and then the accumulator after each element, so `[1, 2, 3].scan(0, |a, x| a + x)` is `[0, 1, 3, 6]`. `reduce(f)` is `None` for an empty list, and otherwise the fold of the other elements onto the first. `group_by(key)` and `count_by(key)` give a map whose keys come in order of first appearance, each list in order. `List.repeat(x, n)` and `List.generate(n, f)` give `[]` when `n <= 0`. `generate` calls `f(0)` to `f(n - 1)` in order. `zip(other)` is as long as the shorter list.

Tests: [ported/bottles.lt](../conformance/ported/bottles.lt), [ported/hundred_doors.lt](../conformance/ported/hundred_doors.lt), [ported/knapsack.lt](../conformance/ported/knapsack.lt), [ported/luhn.lt](../conformance/ported/luhn.lt), [ported/perfect_numbers.lt](../conformance/ported/perfect_numbers.lt), [std/filter_map.lt](../conformance/std/filter_map.lt), [std/filter_map_rejected.lt](../conformance/std/filter_map_rejected.lt), [std/list_callbacks.lt](../conformance/std/list_callbacks.lt), [std/list_functions.lt](../conformance/std/list_functions.lt).

<a id="std.list-slicing"></a>
`take(n)`, `skip(n)`, `take_last(n)`, `skip_last(n)`, `split_at(n)` and `truncate(n)` clamp `n` to `0 ≤ n ≤ len`, and never panic. `split_at(n)` is `(take(n), skip(n))`. `chunks(n)` gives consecutive pieces of `n` elements, the last one shorter when `n` doesn't divide the length. `windows(n)` gives every run of `n` consecutive elements, in order, and `[]` when the list is shorter than `n`. Both panic when `n < 1`, with the messages `chunks needs a size of at least 1, not {n}` and `windows needs a size of at least 1, not {n}`. `take_while(p)` gives the longest prefix whose elements satisfy `p`, and `skip_while(p)` the rest. `first()` and `last()` give the first and the last element, and `None` for an empty list. `concat(other)` gives the receiver's elements, then those of `other`. `List.flatten(lists)` gives the elements of each list in turn, and `List.unzip(pairs)` the list of the pairs' first elements and the list of their second ones. `enumerate(start)` gives each element paired with its index plus `start`, and panics with `overflow` when that sum leaves `i64`.

Tests: [ported/hailstone.lt](../conformance/ported/hailstone.lt), [ported/pascal.lt](../conformance/ported/pascal.lt), [std/list_chunks_panic.lt](../conformance/std/list_chunks_panic.lt), [std/list_ends_and_joins.lt](../conformance/std/list_ends_and_joins.lt), [std/list_functions.lt](../conformance/std/list_functions.lt), [std/list_windows_panic.lt](../conformance/std/list_windows_panic.lt).

<a id="std.list-searching"></a>
`find(p)`, `find_index(p)` and, for `T: Eq`, `index_of(x)` give the first element or index that matches. `min_by(key)`, `max_by(key)` and, for `T: Ord`, `min()` and `max()` give the first smallest or largest element, and `None` for an empty list. For `T: Ord`, `binary_search(x)` gives, in a sorted list, the index of the first element for which `compare` with `x` gives `Equal`, or `None`. For `T: Ord`, `is_sorted()` is whether no element is greater than the one after it. For a list whose elements that satisfy `p` all come before those that don't, `partition_point(p)` gives the index of the first element that doesn't. It finds it by binary search, so `p` is called only on the elements that the search visits. For `T: Eq`, `contains(x)`, `starts_with(prefix)` and `ends_with(suffix)` compare elements with `eq`.

Tests: [ported/binary_search.lt](../conformance/ported/binary_search.lt), [ported/hailstone.lt](../conformance/ported/hailstone.lt), [std/list_callbacks.lt](../conformance/std/list_callbacks.lt), [std/list_functions.lt](../conformance/std/list_functions.lt), [std/list_sorting.lt](../conformance/std/list_sorting.lt).

<a id="std.list-sorting"></a>
`sorted_by(key)` and `sorted_desc_by(key)` give the elements in ascending and in descending order of `key`. For `T: Ord`, `sorted()` and `sorted_desc()` give them in ascending and in descending order. Each is stable: elements of equal keys keep their order. `sorted_with(cmp)` gives the elements in the order that `cmp` gives, and is stable. Its calls of `cmp` are those of the top-down merge sort of its source. `sort_by`, `sort_desc_by`, `sort`, `sort_desc` and `sort_with` replace the receiver with what the matching participle gives. Elements and keys are ordered by `Ord.compare` ([traits.floats](11-traits.md#traits.floats)). A written `Ord` whose `compare` isn't a total preorder leaves the order of `sorted`, `sorted_desc`, `sorted_by` and `sorted_desc_by` unspecified, but each still gives every element of the receiver exactly once.

Tests: [ported/word_frequency.lt](../conformance/ported/word_frequency.lt), [std/list_sorting.lt](../conformance/std/list_sorting.lt), [std/sort_in_place.lt](../conformance/std/sort_in_place.lt), [std/sort_through_inout.lt](../conformance/std/sort_through_inout.lt), [std/sort_with_any_order.lt](../conformance/std/sort_with_any_order.lt), [std/sorting.lt](../conformance/std/sorting.lt).

<a id="std.list-changes"></a>
`swap(i, j)` swaps two elements, and panics with `bounds` unless both indexes are valid. `extend(other)` appends the elements of `other`, and `clear()` removes every element. `retain(keep)` keeps the elements that satisfy `keep`, in order. For `T: Eq`, `deduped()` keeps each run of equal neighbours once. For `T: Eq + Hash`, `distinct()` keeps the first occurrence of each element, in order. `reverse`, `dedup`, `truncate` and the sorting verbs change the receiver as [std.method-names](#std.method-names) says.

Tests: [ported/insertion_sort.lt](../conformance/ported/insertion_sort.lt), [std/list_functions.lt](../conformance/std/list_functions.lt), [std/list_swap_bounds.lt](../conformance/std/list_swap_bounds.lt), [std/participles_copy.lt](../conformance/std/participles_copy.lt), [std/retain_with_raising_keep.lt](../conformance/std/retain_with_raising_keep.lt), [std/sort_in_place.lt](../conformance/std/sort_in_place.lt), [std/sort_through_inout.lt](../conformance/std/sort_through_inout.lt).

## Maps

<a id="std.maps"></a>
A `Map<K, V>` keeps its entries in insertion order. Every iteration follows that order: a `for` over the map ([expressions.for-iterables](08-expressions.md#expressions.for-iterables)), `entries()`, `keys()`, `values()` and `Show`. `insert(k, v)` and `m[k] = v` set the value of `k`, and a key that already has an entry keeps its position. `remove(k)` removes the entry and gives its value, and a key inserted again after its removal goes to the end. `get(k)` is `None` for a missing key, even when the map has a default. `contains(k)` is whether `k` has an entry. `m[k]` gives the value of `k`. For a missing key, it gives the default when the map has one, without inserting it, and otherwise panics with `missing-key`. `Map.with_default(d)` gives an empty map that stores the default `d`. The default takes no part in the map's equality or its `Show` ([traits.map-equality](11-traits.md#traits.map-equality)). `entries`, `keys` and `values` are written in Stilt, and every other function of this paragraph is native.

Tests: [effects/panic_missing_key.lt](../conformance/effects/panic_missing_key.lt), [expressions/less_than_not_generics.lt](../conformance/expressions/less_than_not_generics.lt), [expressions/loop_forms.lt](../conformance/expressions/loop_forms.lt), [ported/word_frequency.lt](../conformance/ported/word_frequency.lt), [procedural/numbers](../conformance/procedural/numbers/), [std/map_defaults.lt](../conformance/std/map_defaults.lt), [std/map_order.lt](../conformance/std/map_order.lt), [std/maps.lt](../conformance/std/maps.lt), [std/missing_key.lt](../conformance/std/missing_key.lt), [std/no_panics.lt](../conformance/std/no_panics.lt), [std/string_index.lt](../conformance/std/string_index.lt), [traits/map_equality.lt](../conformance/traits/map_equality.lt).

<a id="std.map-key-bounds"></a>
Every operation that finds a key requires `K: Eq + Hash`. These operations are:

- every method of `Map`, including `Map.new` and `Map.with_default`;
- `m[k]`, as a value and as a place;
- `==` and `!=` on maps, so `Map<K, V>` implements `Eq` only when `K` implements `Hash` too.

A use whose key type doesn't meet the bound is E0318, *unsatisfied bound*, at the use ([traits.unsatisfied-bounds](11-traits.md#traits.unsatisfied-bounds)). So `m[1.0]` on a `Map<f64, str>` is E0318, since floats don't implement `Hash`. Iterating over a map and showing it find no key, and need no bound, so `fn dump<K: Show, V: Show>(m: Map<K, V>)` may do both. A function generic in a map's key type declares the bound where it finds keys, as in `fn get<K: Eq + Hash, V>(m: Map<K, V>, k: K) -> V { m[k] }`.

Tests: [std/map_float_key_equality.lt](../conformance/std/map_float_key_equality.lt), [std/map_float_key_index.lt](../conformance/std/map_float_key_index.lt), [std/map_float_key_iterate_and_show.lt](../conformance/std/map_float_key_iterate_and_show.lt), [std/map_float_key_store.lt](../conformance/std/map_float_key_store.lt), [std/map_generic_key_bounded.lt](../conformance/std/map_generic_key_bounded.lt), [std/map_generic_key_unbounded.lt](../conformance/std/map_generic_key_unbounded.lt), [std/map_new_float_key.lt](../conformance/std/map_new_float_key.lt), [traits/bound_reported_once.lt](../conformance/traits/bound_reported_once.lt), [traits/bounds_of_conditional_impl.lt](../conformance/traits/bounds_of_conditional_impl.lt).

<a id="std.finding-keys"></a>
The operations on a key are `contains`, `get`, `insert`, `remove`, `m[k]` and `m[k] = v`. Each calls the key type's `hash` once, on the key. Then it calls `eq` on each stored key of the same hash, in insertion order, until a call returns `true`. The key is the receiver of each call, and the stored key its argument. `m[k] += v` reads `m[k]` and then stores it, so it finds the key twice ([values.compound-assignment-order](05-values.md#values.compound-assignment-order)). A key that `insert` finds keeps the stored key, as well as its position. An `inout` argument `m[k]` is written back as `m[k] = v` is when the call ends. So it inserts `k`, with the default when the callee leaves the value as it was. Which stored keys share a hash is unspecified. If written impls break the law that equal values hash equally, or a key type's `eq` can panic, an operation's outcome that depends on those comparisons is unspecified ([traits.hash-follows-written-eq](11-traits.md#traits.hash-follows-written-eq)).

Tests: [std/inout_map_default.lt](../conformance/std/inout_map_default.lt), [std/map_compares_in_insertion_order.lt](../conformance/std/map_compares_in_insertion_order.lt), [std/map_compares_only_equal_hashes.lt](../conformance/std/map_compares_only_equal_hashes.lt), [std/map_float_key_index.lt](../conformance/std/map_float_key_index.lt), [std/map_float_key_iterate_and_show.lt](../conformance/std/map_float_key_iterate_and_show.lt), [std/map_float_key_store.lt](../conformance/std/map_float_key_store.lt), [std/map_hashes_every_key.lt](../conformance/std/map_hashes_every_key.lt), [std/map_keeps_stored_key.lt](../conformance/std/map_keeps_stored_key.lt), [std/structural_keys.lt](../conformance/std/structural_keys.lt), [traits/structural_hash_reaches_component.lt](../conformance/traits/structural_hash_reaches_component.lt), [traits/written_eq_with_hash.lt](../conformance/traits/written_eq_with_hash.lt), [traits/written_eq_without_hash.lt](../conformance/traits/written_eq_without_hash.lt), [values/compound_reads_after_value.lt](../conformance/values/compound_reads_after_value.lt), [values/inout_map_entry.lt](../conformance/values/inout_map_entry.lt), [values/inout_missing_key.lt](../conformance/values/inout_missing_key.lt), [values/map_compound_order.lt](../conformance/values/map_compound_order.lt).

<a id="std.map-element-places"></a>
An assignment to a place that goes through a map element, as `m[k].f = v`, reads `m[k]` as an expression would. It then stores the changed value back with `m[k] = …`. So it panics with `missing-key` when `k` is absent and the map has no default, and starts from the default otherwise. Under `without panic`, such a place counts as indexing ([effects.panicking-operations](12-effects.md#effects.panicking-operations)).

Tests: [effects/without_panic_map_element_place.lt](../conformance/effects/without_panic_map_element_place.lt), [ported/word_frequency.lt](../conformance/ported/word_frequency.lt), [std/map_element_place_default.lt](../conformance/std/map_element_place_default.lt), [std/map_element_place_missing_key.lt](../conformance/std/map_element_place_missing_key.lt).

<a id="std.map-functions"></a>
The functions of this paragraph are written in Stilt. `Map.from_entries(entries)` gives the map that inserting the entries in order gives. So a later value of a key replaces an earlier one, in its position. `get_or(k, d)` gives the value of `k`, or `d`. `get_or_insert(k, d)` inserts `d` for a missing `k`, then gives the value of `k`. Both do so whether or not the map has a default. `merged(other)` and `extend(other)` insert each entry of `other` in turn, so the values of `other` win and its new keys come after. `retain(keep)` and `filter(keep)` keep the entries whose key and value satisfy `keep`, in order. `map_values(f)` gives each key with `f` of its value. `clear()` removes every entry. A function that returns a new map of the same type keeps the receiver's default, while `from_entries` and `map_values` give a map without one.

Tests: [std/map_functions.lt](../conformance/std/map_functions.lt), [std/map_values_drops_default.lt](../conformance/std/map_values_drops_default.lt), [std/participles_copy.lt](../conformance/std/participles_copy.lt).

## Sets

<a id="std.sets"></a>
`Set<T>` is declared in `std.prelude` as `pub type Set<T> = { elements: Map<T, ()> }`, a prelude type ([program.contents](04-programs.md#program.contents)). Its elements are the keys of `elements`, so they keep insertion order. Its functions are written in Stilt in `impl<T: Eq + Hash> Set<T>`. They are `Set.new()`, `Set.from_list(xs)`, `len`, `is_empty`, `contains`, `insert(x)`, `remove(x)`, `to_list()`, `filter(keep)`, `map(f)`, `is_subset`, `is_superset` and `is_disjoint`. `Set.from_list(xs)` holds the elements of the list in order of first appearance. `insert(x)` adds `x` at the end when it is absent. `remove(x)` takes `x` out when it is present and returns `()`; `contains` tells whether it was there. The results of `map(f)` come in order of first appearance.

`union(other)` gives the receiver's elements, then those of `other` that it lacks. `intersection(other)` and `difference(other)` give the receiver's elements that are, and that aren't, in `other`, in order. `symmetric_difference(other)` gives the receiver's elements that aren't in `other`, then those of `other` that aren't in the receiver. A set isn't iterable, so a `for` iterates over its `to_list()` ([expressions.for-iterables](08-expressions.md#expressions.for-iterables)).

Tests: [ported/happy_numbers.lt](../conformance/ported/happy_numbers.lt), [procedural/numbers](../conformance/procedural/numbers/), [std/set_functions.lt](../conformance/std/set_functions.lt), [std/sets.lt](../conformance/std/sets.lt).

<a id="std.set-impls"></a>
`Set` gets the structural `Eq` of its record, which compares the maps. So two sets are equal when they hold the same elements, in any order. It has no `Ord`, since a map has none ([traits.structural-impls](11-traits.md#traits.structural-impls)). Its `Hash` and `Show` impls are written in `std.prelude`. `Hash` adds the elements' hashes with `+%`, so equal sets hash equally and a set can be a map key. `Show` prints `Set([1, 2])`: its elements in order, shown nested.

Tests: [std/sets.lt](../conformance/std/sets.lt).

## `Option`, `Result` and `Ordering`

<a id="std.option-result-and-ordering"></a>
`std.prelude` declares `pub type Option<T> = | None | Some(T)`, `pub type Result<T, E> = | Ok(T) | Err(E)` and `pub type Ordering = | Less | Equal | Greater`. Their order of declaration fixes their structural order ([traits.structural-impls](11-traits.md#traits.structural-impls)), so `None < Some(0)` and `Ok(1) < Err(0)`. Their methods are written in Stilt. `Option` has `is_some`, `is_none`, `map`, `filter`, `unwrap_or`, `ok_or`, `unwrap` and `expect`. `Result` has `is_ok`, `is_err`, `ok`, `err`, `map`, `map_err`, `get`, `unwrap`, `expect` and `Result.of`. `unwrap()` and `expect(msg)` give the value of a `Some` or an `Ok`. On a `None` or an `Err`, they panic with the kind `unwrap`, `expect` with the detail `msg` ([program.panic-report](04-programs.md#program.panic-report)). `r.get()` gives the value of an `Ok` and raises the error of an `Err`. `Result.of(f)` calls `f` and captures its raise as an `Err` ([effects.result](12-effects.md#effects.result)). `opt.filter(keep)` calls `keep` once on the value of a `Some`, and never on a `None`. It is `None` unless the value satisfies `keep`.

Tests: [effects/panic_expect.lt](../conformance/effects/panic_expect.lt), [effects/panic_expect_err.lt](../conformance/effects/panic_expect_err.lt), [effects/panic_unwrap.lt](../conformance/effects/panic_unwrap.lt), [effects/panic_unwrap_err.lt](../conformance/effects/panic_unwrap_err.lt), [effects/passed_to_result_of_paired.lt](../conformance/effects/passed_to_result_of_paired.lt), [effects/passed_to_result_of_unpaired.lt](../conformance/effects/passed_to_result_of_unpaired.lt), [effects/results.lt](../conformance/effects/results.lt), [effects/without_panic_unwrap.lt](../conformance/effects/without_panic_unwrap.lt), [expressions/fields_through_options_missing.lt](../conformance/expressions/fields_through_options_missing.lt), [ported/binary_search.lt](../conformance/ported/binary_search.lt), [std/callback_order.lt](../conformance/std/callback_order.lt), [std/filter_map.lt](../conformance/std/filter_map.lt), [std/list_edges.lt](../conformance/std/list_edges.lt), [std/option_and_result.lt](../conformance/std/option_and_result.lt), [std/option_filter.lt](../conformance/std/option_filter.lt), [std/option_filter_rejected.lt](../conformance/std/option_filter_rejected.lt), [std/result_get_escapes_main.lt](../conformance/std/result_get_escapes_main.lt), [std/sorting.lt](../conformance/std/sorting.lt), [std/unwrap_values.lt](../conformance/std/unwrap_values.lt), [traits/structural_eq_ord_hash.lt](../conformance/traits/structural_eq_ord_hash.lt).

<a id="std.option-result-functions"></a>
`Option` also has these methods:

- `or(other)`, which is `self` when it is a `Some`, and `other` otherwise;
- `zip(other)`, both values when both are `Some`s;
- `is_some_and(p)`, whether `self` is a `Some` whose value satisfies `p`, calling `p` only on a `Some`;
- `to_list()`, `[x]` for `Some(x)` and `[]` for `None`.

`Option.all(options)` gives the values when every element is a `Some`. `Result.all(results)` gives the values when every element is an `Ok`, and otherwise the first `Err`. `Result.partition(results)` gives the values of the `Ok`s and the errors of the `Err`s, in order. The method `unwrap_or(d)` of `Result` is the value of an `Ok`, or `d`. The method `reversed()` of `Ordering` swaps `Less` and `Greater`. Its `then(other)` is `self` unless it is `Equal`, and then `other`, which orders by a second key.

Tests: [std/option_callback_order.lt](../conformance/std/option_callback_order.lt), [std/option_result_ordering.lt](../conformance/std/option_result_ordering.lt), [std/participles_copy.lt](../conformance/std/participles_copy.lt).

## Showing and formatting

<a id="std.show-output"></a>
The prelude's impls of `Show` and the structural ones ([traits.show](11-traits.md#traits.show)) give this output:

| Type | Output |
| --- | --- |
| Integers, floats | As [numbers.printing-integers](06-numbers.md#numbers.printing-integers) and [numbers.printing-floats](06-numbers.md#numbers.printing-floats) give |
| `bool` | `true`, `false` |
| `str` | `ana` at the top level, and `"ana"` nested inside another value |
| `()` | `()` |
| Tuples | `(1, "a")`, `(1,)` |
| `List` | `[1, 2]`, `[]` |
| `Map` | `{"a": 1, "b": 2}`, `{}`, in insertion order |
| `Set` | `Set([1, 2])`, `Set([])`, in insertion order, its elements shown nested |
| Variants | `Some(3)`, `None`, `Node(Leaf, 1, Leaf)` |
| Records | `Order { customer: "ana", qty: 3, price: 2.5 }`, `Empty {}` |
| `collections.Deque` | `Deque([1, 2])`, front first |
| `collections.Heap` | `Heap([1, 2])`, in ascending order |
| `random.Rng` | As a record: `Rng { state: 7 }` |
| `clock.Duration` | `1.5s`, `250µs`, `0ns`, as [std.durations](#std.durations) gives it |
| `clock.DateTime` | `2025-11-15T09:30:00.25Z`, as `to_rfc3339` writes it ([std.rfc-3339](#std.rfc-3339)) |

Tests: [std/collections.lt](../conformance/std/collections.lt), [std/map_keeps_stored_key.lt](../conformance/std/map_keeps_stored_key.lt), [std/map_order.lt](../conformance/std/map_order.lt), [std/maps.lt](../conformance/std/maps.lt), [std/random.lt](../conformance/std/random.lt), [std/set_functions.lt](../conformance/std/set_functions.lt), [std/sets.lt](../conformance/std/sets.lt), [std/show.lt](../conformance/std/show.lt), [std/show_every_type.lt](../conformance/std/show_every_type.lt), [traits/nested_impls_shown.lt](../conformance/traits/nested_impls_shown.lt), [traits/structural_show.lt](../conformance/traits/structural_show.lt), [traits/unit_impls.lt](../conformance/traits/unit_impls.lt).

<a id="std.show-names-and-escapes"></a>
Variant and record names are shown unqualified, whatever module declares them, so an `io.NotFound` shows as `NotFound("x.txt")`. A nested string is escaped with `\"`, `\\`, `\n`, `\t`, `\r` and `\0`. Every other character below U+0020, and U+007F, is written as `\u{…}` in lowercase hexadecimal with no leading zeros, as in `\u{1b}`. Every other character is written as itself.

Tests: [std/argument_edges.lt](../conformance/std/argument_edges.lt), [std/arguments.lt](../conformance/std/arguments.lt), [std/invalid_utf8_escapes_main/main.lt](../conformance/std/invalid_utf8_escapes_main/main.lt), [std/io_errors/main.lt](../conformance/std/io_errors/main.lt), [std/read_files/main.lt](../conformance/std/read_files/main.lt), [std/read_line_endings.lt](../conformance/std/read_line_endings.lt), [std/show_every_type.lt](../conformance/std/show_every_type.lt), [std/string_edges.lt](../conformance/std/string_edges.lt), [std/strings.lt](../conformance/std/strings.lt).

<a id="std.width-fill-and-alignment"></a>
A format spec's width, fill and alignment ([lexical.format-specs](02-lexical.md#lexical.format-specs)) apply to a value of any type. They pad its shown text, measured in Unicode scalar values, to at least the width. The default fill is a space. Without an alignment, a splice whose type, where it is written, is a numeric type aligns right. Every other splice aligns left, including a value of a type parameter, even where a numeric type instantiates it. Centred text with an odd amount of padding puts the extra fill character on the right, so `{7:*^4}` prints `*7**`.

Tests: [lexical/spec_zero_numbers.lt](../conformance/lexical/spec_zero_numbers.lt), [ported/ethiopian_multiplication.lt](../conformance/ported/ethiopian_multiplication.lt), [std/format_alignment.lt](../conformance/std/format_alignment.lt), [std/format_alignment_generic.lt](../conformance/std/format_alignment_generic.lt), [std/format_integer_kinds.lt](../conformance/std/format_integer_kinds.lt), [std/format_special_values.lt](../conformance/std/format_special_values.lt), [std/format_specs.lt](../conformance/std/format_specs.lt), [std/format_specs_rejected.lt](../conformance/std/format_specs_rejected.lt), [types/format_specs.lt](../conformance/types/format_specs.lt).

<a id="std.precision"></a>
A precision without a kind applies only to floats. It prints fixed notation with exactly that many fractional digits, rounding the exact binary value half to even, and with a precision of 0 it prints no decimal point. A negative value keeps its `-` even when it rounds to zero, so `{-0.001:.2}` prints `-0.00`.

Tests: [lexical/spec_zero_numbers.lt](../conformance/lexical/spec_zero_numbers.lt), [ported/temperature_conversion.lt](../conformance/ported/temperature_conversion.lt), [std/format_precision.lt](../conformance/std/format_precision.lt), [std/format_special_values.lt](../conformance/std/format_special_values.lt), [std/format_specs.lt](../conformance/std/format_specs.lt), [std/format_specs_rejected.lt](../conformance/std/format_specs_rejected.lt), [types/format_specs.lt](../conformance/types/format_specs.lt).

<a id="std.integer-kinds"></a>
The kinds `x`, `X`, `o` and `b` apply only to integers, and never with a precision. They print the value in lowercase hexadecimal, uppercase hexadecimal, octal and binary, with no prefix and no leading zeros, so `{255:x}` prints `ff` and `{0:b}` prints `0`. A negative value prints as its two's complement at its type's width, so `{-1:x}` prints `ffffffffffffffff` for an `i64`.

Tests: [std/format_integer_kind_digits.lt](../conformance/std/format_integer_kind_digits.lt), [std/format_integer_kinds.lt](../conformance/std/format_integer_kinds.lt), [std/format_specs.lt](../conformance/std/format_specs.lt), [std/format_specs_rejected.lt](../conformance/std/format_specs_rejected.lt), [types/format_specs.lt](../conformance/types/format_specs.lt).

<a id="std.scientific-notation"></a>
The kind `e` applies only to floats, and prints scientific notation in the form of [numbers.float-notation](06-numbers.md#numbers.float-notation). Without a precision, its digits are the shortest ones ([numbers.float-digits](06-numbers.md#numbers.float-digits)). With a precision, exactly that many digits follow the decimal point, rounding the exact binary value half to even, so `{12345.0:.2e}` prints `1.23e4`. A zero prints as `0e0` or `-0e0`. With a precision, it prints with zeros after the point, as `{0.0:.2e}` prints `0.00e0`.

Tests: [std/format_scientific.lt](../conformance/std/format_scientific.lt), [std/format_special_values.lt](../conformance/std/format_special_values.lt), [std/format_specs.lt](../conformance/std/format_specs.lt), [std/format_specs_rejected.lt](../conformance/std/format_specs_rejected.lt), [types/format_specs.lt](../conformance/types/format_specs.lt).

<a id="std.format-special-values"></a>
NaN and the infinities print as `nan`, `inf` and `-inf` under every float spec, and width, fill and alignment still apply to them.

Tests: [std/format_special_values.lt](../conformance/std/format_special_values.lt), [std/format_specs.lt](../conformance/std/format_specs.lt).

<a id="std.invalid-specs"></a>
A spec that doesn't apply to its operand's type is E0325, *invalid format spec*, at the interpolated expression. A spec doesn't apply in these cases:

- a precision without a kind, or the kind `e`, on anything but a float;
- `x`, `X`, `o` or `b` on anything but an integer, or with a precision.

The operand's type is the one its whole body gives it, after the defaults of [numbers.literal-defaults](06-numbers.md#numbers.literal-defaults), so a spec never decides the type of a literal. After `let x = 5`, `"{x:.2}"` is E0325 unless the rest of the body makes `x` a float. A spec that breaks the grammar of specs is E0007, *malformed format spec* ([lexical.format-specs](02-lexical.md#lexical.format-specs)).

Tests: [std/format_alignment.lt](../conformance/std/format_alignment.lt), [std/format_integer_kinds.lt](../conformance/std/format_integer_kinds.lt), [std/format_spec_defaulted_type.lt](../conformance/std/format_spec_defaulted_type.lt), [std/format_spec_settled_type.lt](../conformance/std/format_spec_settled_type.lt), [std/format_specs_rejected.lt](../conformance/std/format_specs_rejected.lt), [types/format_specs.lt](../conformance/types/format_specs.lt).

## Input and output

<a id="std.read-line"></a>
`io.read_line()` gives one line of stdin. The line leaves out the `\n` that ends it, and a `\r` that ends what is left, even on a last line with no `\n`. It is `None` at the end of the input and when stdin can't be read. Each maximal subpart of an invalid UTF-8 sequence becomes one U+FFFD ([std.code-points](#std.code-points)). `read_line` is native and performs `io`.

Tests: [std/read_line.lt](../conformance/std/read_line.lt), [std/read_line_bytes.lt](../conformance/std/read_line_bytes.lt), [std/read_line_endings.lt](../conformance/std/read_line_endings.lt), [std/read_line_without_input.lt](../conformance/std/read_line_without_input.lt).

<a id="std.io"></a>
`std.io` also has these native functions:

- `write(s)` and `ewrite(s)`, which write `s` to stdout and to stderr with no newline;
- `flush()`;
- `read_all()`, the rest of stdin after what has been read, with invalid UTF-8 replaced, and `""` at the end of the input and when stdin can't be read;
- `poll_line()`, which never waits. When a whole line, or the last line before the end of the input, is waiting, it reads it as `read_line` does. Otherwise it gives `None`.

`read_lines()`, written in Stilt, calls `read_line` until it gives `None`. Every function of `std.io` performs `io`. Text that `write` writes reaches stdout as printed text does ([program.prelude-functions](04-programs.md#program.prelude-functions)). Each line reaches it with its newline, and the rest with the next newline, at `flush()`, before a read of stdin, or when the process ends. `read_line`, `read_all` and `poll_line` write out stdout before they read, so a prompt shows before the program waits for its answer. They read one stream, so a line that one of them has read is never read again by another.

Tests: [std/io_flush.lt](../conformance/std/io_flush.lt), [std/io_poll_line.lt](../conformance/std/io_poll_line.lt), [std/io_poll_line_empty.lt](../conformance/std/io_poll_line_empty.lt), [std/io_poll_line_mixed.lt](../conformance/std/io_poll_line_mixed.lt), [std/io_read_all.lt](../conformance/std/io_read_all.lt), [std/io_read_lines.lt](../conformance/std/io_read_lines.lt), [std/io_write.lt](../conformance/std/io_write.lt).

Checked by: for writing out before a read and `poll_line`'s not waiting, which the protocol can't observe, since it supplies stdin whole and captures stdout whole, the toolchain's tests of runs that wait for a line (`compiler/stilt-cli/tests/run.rs`) and of `poll_line` (`compiler/stilt-cli/tests/streams.rs`).

<a id="std.io-errors"></a>
`std.io` declares `pub type IoError = | NotFound(path: str) | PermissionDenied(path: str) | InvalidUtf8(path: str) | Other(path: str)`, the error of every I/O operation. A module that imports `std.io` writes it `io.IoError`, and its variants as `io.NotFound`. `NotFound` means that the file, or a directory on its path, doesn't exist. `PermissionDenied` means that access was refused. `InvalidUtf8` means that `read` or `read_lines` found bytes that aren't UTF-8. `Other` is every other failure, among them a path that names a directory, and a path that holds U+0000, which names no file. An `IoError` that escapes `main` is shown unqualified ([program.exit-statuses](04-programs.md#program.exit-statuses)).

Tests: [program/raise_escapes_main.lt](../conformance/program/raise_escapes_main.lt), [std/io_errors/main.lt](../conformance/std/io_errors/main.lt), [std/read_files/main.lt](../conformance/std/read_files/main.lt).

<a id="std.fs"></a>
Each function of `std.fs` except the path functions ([std.fs-paths](#std.fs-paths)) is native and performs `io`. Each whose row holds `raise<io.IoError>` raises with the path it was given:

- `NotFound` when the path, or a directory on it, doesn't exist;
- `PermissionDenied` when access is refused;
- `Other` for every other failure.

`rename` raises with `from` when `from` doesn't exist, and otherwise with `to`. `copy` raises with the path whose read or write failed. `read(path)` gives a file's contents, `read_lines(path)` its lines as `lines()` splits them, and `read_bytes(path)` its bytes. `write(path, text)` and `write_bytes(path, bytes)` create or replace a file. `append(path, text)` appends to a file, and creates it when it doesn't exist. `copy(from, to)`, written in Stilt, writes the bytes of `from` to `to`. `exists(path)`, `is_file(path)` and `is_dir(path)` are whether anything, a file or a directory is at `path`, following symbolic links. They are `false` when that can't be found out.

Tests: [std/fs_files/main.lt](../conformance/std/fs_files/main.lt), [std/io_errors/main.lt](../conformance/std/io_errors/main.lt), [std/read_files/main.lt](../conformance/std/read_files/main.lt).

<a id="std.directories"></a>
`fs.list_dir(path)` gives the names of a directory's entries, without `.` and `..`, with invalid UTF-8 replaced, sorted by their bytes. It raises `Other` for a path that names a file. `fs.create_dir(path)` creates the directory and every missing directory on its path. A directory that already exists at `path` is no error, and anything else at `path` raises `Other`. `fs.remove(path)` removes a file, or a directory when it is empty, and raises `Other` for a directory that isn't empty. `fs.remove_all(path)` removes a file, or a directory and everything in it, never following a symbolic link. It raises `NotFound` for a path that doesn't exist. `fs.rename(from, to)` moves `from` to `to`, replacing a file at `to`.

Tests: [std/fs_files/main.lt](../conformance/std/fs_files/main.lt).

<a id="std.fs-paths"></a>
The path functions of `std.fs` are written in Stilt and perform nothing. `join(base, path)` is one of these:

- `path`, when `path` starts with `/` or `base` is empty;
- `base` followed by `path`, when `base` ends with `/`;
- the two with a `/` between them, otherwise.

`file_name(path)` is the text after the last `/`. It is `""` when `path` ends with a `/`, and the whole path when it has none. `parent(path)` is the text up to the last `/`, without the `/`s that end it unless it is only `/`s. It is `""` when there is no `/`. So `parent("a/b")` is `"a"`, `parent("/a")` is `"/"` and `parent("b")` is `""`. `extension(path)` is the text after the last `.` of the file name, when that `.` isn't the name's first character. So `extension("a.tar.gz")` is `Some("gz")` and `extension(".profile")` is `None`.

Tests: [std/fs_paths.lt](../conformance/std/fs_paths.lt).

<a id="std.cli"></a>
`cli.args()` gives the program's arguments, without the program's name, with invalid UTF-8 replaced ([std.code-points](#std.code-points)). `cli.arg(i)`, written in Stilt, is `args().get(i)`. `cli.env(name)` gives the value of the environment variable `name`, with invalid UTF-8 replaced. It is `None` when the variable isn't set, and when `name` is empty or holds `=` or U+0000. Each performs `io`.

Tests: [std/argument_edges.lt](../conformance/std/argument_edges.lt), [std/arguments.lt](../conformance/std/arguments.lt), [std/cli_env.lt](../conformance/std/cli_env.lt), [std/invalid_utf8_escapes_main/main.lt](../conformance/std/invalid_utf8_escapes_main/main.lt), [std/no_arguments.lt](../conformance/std/no_arguments.lt).

## Time

<a id="std.clock"></a>
`clock.unix_ms()` gives the milliseconds since 1970-01-01T00:00:00Z by the system's clock. `clock.monotonic_ns()` gives the nanoseconds since an unspecified start, which never decrease while the program runs. `clock.sleep_ms(ms)` waits at least `ms` milliseconds, and returns at once when `ms <= 0`. Each is native and performs `io`. Every other function of `std.clock` is written in Stilt. The functions of [std.instants](#std.instants) and [std.date-times](#std.date-times) that read the clock or wait call these three.

Tests: [std/clock.lt](../conformance/std/clock.lt).

<a id="std.durations"></a>
`std.clock` declares `pub type Duration = { ns: i64 }`, a length of time in nanoseconds, which may be negative. `Duration.from_ns(n)`, `from_us(n)`, `from_ms(n)`, `from_seconds(n)`, `from_minutes(n)` and `from_hours(n)` are the duration of `n` of their unit. `whole_ms()` and `whole_seconds()` are the whole milliseconds and seconds in a duration, rounded toward zero. `seconds()` is its length in seconds: `ns` converted to an `f64` and divided by `1e9`. `plus(other)` and `minus(other)` are the sum and the difference of two durations. `from_us` to `from_hours`, `plus` and `minus` panic with `overflow` when the result doesn't fit in an `i64` of nanoseconds, as `*`, `+` and `-` do.

A duration gets the structural `Eq`, `Ord` and `Hash` of its record, so durations order by length. Its `Show` writes its length in the largest of the units `s`, `ms`, `µs` and `ns` that it reaches. The length is a decimal of that unit whose fraction has no trailing zeros, and no point when the fraction is zero, with a `-` when the duration is negative. So `Duration.from_ms(1500)` shows as `1.5s`, `Duration.from_us(250)` as `250µs` and a zero as `0ns`.

Tests: [time/durations.lt](../conformance/time/durations.lt), [time/durations_overflow.lt](../conformance/time/durations_overflow.lt).

<a id="std.instants"></a>
`pub type Instant = { ns: i64 }` is a reading of the monotonic clock. `clock.now()` reads it, as `monotonic_ns()` does. `elapsed()` is the duration from an instant to a new reading. `since(earlier)` is the duration from `earlier` to an instant, and `plus(d)` the instant `d` after it. `clock.sleep(d)` waits at least `d`. It calls `sleep_ms` with the milliseconds of `d` rounded up, so it returns at once when `d` isn't positive. `now`, `elapsed` and `sleep` perform `io`, and have the capability `clock` through the natives they call ([facts.capabilities](15-facts.md#facts.capabilities)).

Tests: [time/instants.lt](../conformance/time/instants.lt).

<a id="std.date-times"></a>
`pub type DateTime = { year: i64, month: i64, day: i64, hour: i64, minute: i64, second: i64, nanosecond: i64 }` is a date and a time of day in UTC. Its calendar is the Gregorian calendar extended to every year, with no leap seconds. `DateTime.now()` is the time that `unix_ms()` reads. `DateTime.from_unix_seconds(s)` and `from_unix_ms(ms)` are the time `s` seconds or `ms` milliseconds after 1970-01-01T00:00:00Z, and before it for a negative count. `unix_seconds()` and `unix_ms()` count back to it, rounded down. `DateTime.of(year, month, day, hour, minute, second)` is the time of those fields and no nanoseconds. It is `None` unless `month` is from 1 to 12, `day` a day of that month, `hour` from 0 to 23, and `minute` and `second` from 0 to 59.

`weekday()` is the day of the week, from 1 for Monday to 7 for Sunday. `plus(d)` is the time `d` later, and `since(earlier)` the duration from `earlier`. `plus` and `since` panic with `overflow` when a count of seconds or nanoseconds doesn't fit in an `i64`. A time gets the structural `Eq`, `Ord` and `Hash` of its record, so times whose fields are in range order chronologically.

Tests: [time/date_times.lt](../conformance/time/date_times.lt).

<a id="std.rfc-3339"></a>
`to_rfc3339()` writes a time as RFC 3339's `date-time` does in UTC, as in `2025-11-15T09:30:00.25Z`. It writes the year in four digits, then the month, the day, `T`, the hour, the minute and the second in two digits each, separated by `-` and `:`. Unless the nanoseconds are zero, a `.` follows, then the nanoseconds as a fraction of a second with no trailing zeros. `Z` ends the text. A year below 0 or above 9999, which RFC 3339 doesn't write, is written with as many digits as it needs, after a `-` when it is negative. The `Show` of `DateTime` writes the same text.

`DateTime.from_rfc3339(text)` reads what RFC 3339's `date-time` writes:

- the date and the time, with `T` or `t` between them;
- after the seconds, optionally, a `.` and at least one digit, of which the first nine count;
- `Z`, `z` or an offset: `+` or `-`, then an hour from 00 to 23, `:` and a minute from 00 to 59. It subtracts the offset from the time to give the time in UTC.

It is `None` for any other text, and when a field is out of the range that `DateTime.of` takes, as the leap second `23:59:60` is.

Tests: [time/rfc_3339.lt](../conformance/time/rfc_3339.lt).

## Running programs

<a id="std.process"></a>
`std.process` runs other programs. It declares `pub type Command = { program: str, args: List<str>, env: List<(str, Option<str>)>, dir: str, input: str }`, a program to run. Its fields are these:

- `program`, the program's name or path;
- `args`, its arguments;
- `env`, the changes it makes to the environment it inherits, `Some(value)` setting a variable and `None` removing it;
- `dir`, its working directory, `""` for the running program's own;
- `input`, the text that `output` gives it as its standard input.

The module declares `pub type Output = { status: i64, stdout: str, stderr: str }`, how a run ended and what it wrote. It declares `pub type Child = { id: i64 }`, a program that runs beside the one that started it. A **status** is the code that a program exited with, from 0 to 255, or `-n` when the signal `n` ended it. Every function of the module except those of [std.process-commands](#std.process-commands) reaches other programs through its natives. These natives perform `io` and have the capability `exec` ([facts.capability-natives](15-facts.md#facts.capability-natives)). None of these functions panics.

Tests: [process/output.lt](../conformance/process/output.lt), [process/status.lt](../conformance/process/status.lt).

<a id="std.process-commands"></a>
The functions of this paragraph are written in Stilt. `Command.new(program)` is the command with no arguments, no changes to the environment, the working directory `""` and the input `""`. `with_arg(arg)` and `with_args(args)` give a command more arguments after its own. `with_env(name, value)` and `without_env(name)` give it a change after its own, which sets the variable `name` to `value` or removes it. `with_dir(dir)` gives it a working directory, and `with_input(input)` an input. `process.run(program, args)` is `Command.new(program).with_args(args).output()`.

Tests: [process/commands.lt](../conformance/process/commands.lt).

<a id="std.process-starting"></a>
A command runs its program with its arguments, in its working directory. Its environment is the running program's, changed by each of the command's changes in order. A program that holds a `/` is a path, relative to the running program's working directory when it doesn't start with one. Any other program is the first file of that name that may be executed in the directories that the `PATH` of the command's environment lists. `PATH` separates them by `:`, they are searched in order, and an empty one names none. A command that can't start raises an `io.IoError` ([std.io-errors](#std.io-errors)), the first of these that applies:

- `Other(program)` when the program, an argument, the directory or a value holds U+0000, or a variable's name is empty or holds `=` or U+0000;
- `NotFound(dir)` when its working directory names no directory;
- `NotFound(program)` when no file is found;
- `PermissionDenied(program)` when the files found may not be executed;
- `Other(program)` for every other failure.

Tests: [process/errors.lt](../conformance/process/errors.lt), [process/output.lt](../conformance/process/output.lt).

<a id="std.process-runs"></a>
`output()` runs a command to its end, with its input as its standard input. It gives an `Output` of its status and of the text it wrote to its standard output and its standard error. Each is read whole, at the same time as the input is written, with invalid UTF-8 replaced ([std.code-points](#std.code-points)). `status()` runs a command to its end with the running program's own standard input, output and error, and gives its status. It first writes out what the program wrote to stdout ([std.io](#std.io)), so what each prints appears in the order they print it.

Tests: [process/output.lt](../conformance/process/output.lt), [process/status.lt](../conformance/process/status.lt).

<a id="std.children"></a>
`spawn()` starts a command without waiting, and gives its `Child`. The child's standard input and output are piped to the program that started it, and its standard error is that program's own. Each method of `Child` takes it `inout`:

- `write(text)` writes `text` to the child's standard input, and raises `Other(program)` when it can't, as when its input is closed;
- `close_input()` closes its standard input, so that it reads to the end;
- `read_line()` gives the next line of its standard output, as `io.read_line` splits and repairs one ([std.read-line](#std.read-line)), and `None` at its end;
- `read_all()` gives the rest of its standard output, and `""` at its end;
- `wait()` closes the child's standard input, reads the rest of its output, waits for it to end and gives its status. `read_line` and `read_all` give that output afterwards, and each call of `wait` gives the same status;
- `kill()` ends the child at once with the signal 9, unless it has ended already, so that `wait` then gives `-9`.

Tests: [process/children.lt](../conformance/process/children.lt).

## The network

<a id="std.net"></a>
`std.net` reaches the network over TCP and UDP. It declares these types:

- `pub type Stream = { id: i64 }`, a connection;
- `pub type Listener = { id: i64 }`, a listener bound to an address;
- `pub type Socket = { id: i64 }`, a UDP socket bound to an address;
- `pub type Datagram = { bytes: List<u8>, from: str }`, a datagram that a socket received.

A stream, a listener and a socket are each a handle that the module's natives know by its number. Every function of the module reaches the network through those natives, which perform `io` and have the capability `net` ([facts.capability-natives](15-facts.md#facts.capability-natives)). None of these functions panics. `net.lookup(host)` gives the addresses of `host`, a name or an address, as text, each once. IPv4 addresses are in dotted decimal, and IPv6 addresses as RFC 5952 writes them. They come in the order that the system's resolver gives them. `lookup` raises `NotFound(host)` when it finds none, as for `""`, and `Other(host)` for a host that holds U+0000.

Tests: [net/datagrams.lt](../conformance/net/datagrams.lt), [net/lookup.lt](../conformance/net/lookup.lt), [net/streams.lt](../conformance/net/streams.lt).

<a id="std.net-listeners"></a>
`net.connect(host, port)` connects to `port` at each address of `host` in turn, until one accepts, and gives the connection. `net.listen(host, port)` binds a listener to `port` at the first address of `host` that it can bind, or to a port that the system picks when `port` is 0. Each raises an `io.IoError` that names `host:port`, as they were given, the first of these that applies:

- `Other` for a port outside 0 to 65535 or a host that holds U+0000;
- `NotFound` when `host` has no address;
- the failure of the last address tried: `PermissionDenied` when the system refuses access to the port, and `Other` for every other failure, a refused connection and a port in use among them.

A listener's `port()` is the port it listens on, and 0 once it is closed. `accept()` waits for the next connection and gives it. It raises `Other` with the listener's `host:port` once the listener is closed. `close()` closes the listener.

Tests: [net/lookup.lt](../conformance/net/lookup.lt), [net/streams.lt](../conformance/net/streams.lt).

<a id="std.net-streams"></a>
A stream's methods take it `inout`, and it reads through a buffer of its own. A stream's **address** is the `host:port` that `connect` was given. For a stream that `accept` gave, it is its peer's address and port, written `ip:port`, with brackets around an IPv6 address. `write(text)` and `write_bytes(bytes)` write whole. They raise `Other` with the stream's address when they can't, as once it is closed. `read_line()` gives the next line that the stream reads, split and repaired as `io.read_line` splits and repairs one ([std.read-line](#std.read-line)), and `None` at the end of what it reads. `read_bytes(n)` gives the next `n` bytes, fewer only at that end, and none when `n` isn't positive. `read_all()` gives what is left until the end, with invalid UTF-8 replaced. A read that fails, and one that a timeout gives up, reads as the end.

`set_timeout(ms)` makes the reads and writes that follow give up after waiting `ms` milliseconds. When `ms <= 0`, they wait as long as they take. `close_write()` closes the stream's writing side, so that the other end reads to its end. `close()` closes the stream, which reads as at its end from then on.

Tests: [net/streams.lt](../conformance/net/streams.lt).

<a id="std.net-datagrams"></a>
`net.socket(host, port)` binds a UDP socket to `port` at the first address of `host` that it can bind, or to a port that the system picks when `port` is 0. It raises as `net.listen` raises ([std.net-listeners](#std.net-listeners)). A socket's methods except `port` take it `inout`. Its `port()` is the port it is bound to, and 0 once it is closed. `send_to(bytes, host, port)` sends `bytes` as one datagram to `port` at each address of `host` in turn, until one takes it. It raises an `io.IoError` that names `host:port`, as they were given, the first of these that applies:

- `Other` for a port outside 0 to 65535 or a host that holds U+0000;
- `NotFound` when `host` has no address;
- `Other` once the socket is closed;
- the system's refusal of the last address tried: `PermissionDenied` when it refuses access, and `Other` for every other refusal, a datagram longer than it sends among them.

A datagram that was sent is not sure to arrive: UDP promises nothing more. `receive()` waits for the next datagram and gives `Some(Datagram { bytes, from })`. `bytes` is the datagram's bytes, of which it keeps at most the first 65,536. `from` is its sender's address, written `ip:port` as a stream's peer is ([std.net-streams](#std.net-streams)). `receive()` gives `None` when the wait fails or a timeout gives it up, and once the socket is closed. `set_timeout(ms)` makes the waits of `receive` and `send_to` that follow give up after `ms` milliseconds. When `ms <= 0`, they wait as long as they take. `close()` closes the socket.

Tests: [net/datagrams.lt](../conformance/net/datagrams.lt).

<a id="std.http"></a>
`std.http` speaks HTTP/1.1 as RFC 9112 writes it. It is written in Stilt on `std.net`, through which its functions that reach a connection have the capability `net`. It speaks no TLS, so its client fetches `http://` URLs only. Each connection carries one request, answered and then closed. The module declares these types:

- `pub type Request = { method: str, target: str, headers: List<(str, str)>, body: str }`;
- `pub type Response = { status: i64, headers: List<(str, str)>, body: str }`;
- `pub type Error = | Io(error: io.IoError) | Url(url: str) | Message(part: str)`.

Headers are in the order they are written. `Io` is a failure of the connection, and `Url` a URL that the client can't fetch. `Message` is a message that isn't HTTP/1.1, with the part of it that isn't. A body is text, read from its bytes with invalid UTF-8 replaced.

Tests: [http/messages.lt](../conformance/http/messages.lt).

<a id="std.http-messages"></a>
`Request.new(method, target)` is the request with no headers and no body. `Response.new(status, body)` is the response with no headers. `with_header(name, value)` gives either a header after its own, and `with_body(body)` gives a request its body. `header(name)` is the value of the first header whose name equals `name` once their ASCII letters are lowered, or `None`. `http.reason(status)` is the reason phrase that RFC 9110 gives each of the common status codes that its source lists, as `OK` for 200 and `Not Found` for 404. For any other code, it is `""`. `write_request(inout conn, request)` writes these, each line ended by `\r\n`:

- the request line `METHOD TARGET HTTP/1.1`;
- each header as `name: value`;
- a `Content-Length` of the body's bytes when the body isn't empty or the method is `POST`, `PUT` or `PATCH`, unless the headers hold one;
- an empty line;
- the body.

`write_response(inout conn, response)` writes the status line `HTTP/1.1 STATUS REASON`, the headers, a `Content-Length` unless they hold one, an empty line and the body. Each raises `Io` when the connection can't be written.

`read_request(inout conn)` reads a request line of three parts separated by single spaces, the last starting with `HTTP/1.`, or raises `Message("request line")`. `read_response(inout conn, method)` reads a status line, or raises `Message("status line")`. The status line is a version starting with `HTTP/1.`, a space and a code of three ASCII digits, then nothing or a space and a reason, which it drops. Each then reads headers up to an empty line, or raises `Message("header")`. Each header is `name:value`, with a name that isn't empty and holds no whitespace at its ends, and a value trimmed of ASCII whitespace. Each then reads a body:

- When `Transfer-Encoding` is `chunked`, in any case, it reads chunks up to a chunk of size 0, or raises `Message("chunk")`. Each chunk is a size in hexadecimal digits, with what follows a `;` dropped, then that many bytes and an empty line. After the chunk of size 0, trailing headers are read and dropped.
- Otherwise, when there is a `Content-Length`, it reads that many bytes. It raises `Message("Content-Length")` unless `str.to_i64` reads the length as an integer from 0, and `Message("body")` when the connection ends first.
- Otherwise, a request has no body, and a response's body is what the connection reads until its end.

A response to `HEAD`, and one with a status of 1xx, 204 or 304, has no body. A connection that ends before a part that the message needs raises `Message` with that part.

Tests: [http/exchange.lt](../conformance/http/exchange.lt), [http/messages.lt](../conformance/http/messages.lt).

<a id="std.http-client"></a>
`http.send(request, url)` connects to the host and the port of `url`. It writes `request` with the target of `url` in place of its own, and with the headers `Host`, the authority of `url`, and `Connection: close` before its own. It then reads the response to the request's method, and closes the connection. `http.get(url)` sends `Request.new("GET", "")`. `http.post(url, content_type, body)` sends a `POST` with the header `Content-Type: content_type` and `body`. A URL is `http://`, its scheme in any case, then an authority and a target:

- the authority runs to the first `/` or `?`. It is a host, or an IPv6 address in brackets, and an optional `:` and port, 80 when there is none;
- the target is the rest, without a `#` and what follows it. It gets a `/` before it when it starts with a `?`, and is `/` when it is empty.

Any other URL raises `Url(url)`: another scheme, `https` among them, an empty host, a user before an `@`, a `:` in a host outside brackets, and a port outside 0 to 65535. A failure of the connection raises `Io`.

Tests: [http/urls.lt](../conformance/http/urls.lt).

Checked by: for a response fetched whole, which no conformance test can wait for, since its sequential run would never serve it, the toolchain's tests of `get` and `post` against a server of the test's own (`compiler/stilt-cli/tests/http.rs`).

<a id="std.http-server"></a>
`serve_one(inout listener, handle)` accepts a connection and reads its request. It writes the response that `handle` gives for the request, with `Connection: close` after its headers. For a request whose reading raises `Message`, it writes a response of 400 with no body instead. It then closes the connection. A failure to accept, to read other than by `Message`, or to write raises. `serve(inout listener, handle)` does what `serve_one` does for each connection in turn, for as long as the program runs, giving up a connection that fails. `handle` is called once for each request that it answers, and its effects pass through to the caller ([std.callbacks](#std.callbacks)).

Tests: [http/exchange.lt](../conformance/http/exchange.lt).

Checked by: for `serve`, which never returns, the toolchain's tests of a server that answers clients of the test's own (`compiler/stilt-cli/tests/http.rs`).

## Random numbers

<a id="std.random"></a>
`std.random` declares `pub type Rng = { state: u64 }`, a pseudo-random generator written in Stilt, so a seed gives the same numbers in every implementation. Every function of the module is written in Stilt except `random.entropy() -> u64 / io`, a number from the system's source of randomness. `Rng.seeded(seed)` is the generator whose state is `seed`, and `Rng.from_entropy()` is `Rng.seeded(entropy())`. `next_u64()` is SplitMix64. It adds `0x9E3779B97F4A7C15` to the state with `+%`, and gives the new state `z` mixed in three steps:

1. `z = (z ^ (z >> 30)) *% 0xBF58476D1CE4E5B9`;
2. `z = (z ^ (z >> 27)) *% 0x94D049BB133111EB`;
3. `z ^ (z >> 31)`.

Every draw changes the generator, so its methods take `inout self`. `Rng` gets the structural impls of its record.

Tests: [std/random.lt](../conformance/std/random.lt).

<a id="std.random-numbers"></a>
`below(n)` gives a number in `0 ..< n`, every one equally likely. Where `m` is `n` as a `u64`, it is the first `next_u64()` that is at least `(0 -% m) % m`, taken modulo `m`. It panics when `n < 1`, with the message `below needs a bound of at least 1, not {n}`. `range(lo, hi)` gives a number in `lo ..< hi`, every one equally likely. It is `lo` plus a number below the width of the range, drawn as `below` draws it, with arithmetic that wraps, so `range(i64.MIN, i64.MAX)` is valid. It panics when `lo >= hi`, with the message `range needs lo < hi, not {lo} and {hi}`. `float()` is the top 53 bits of `next_u64()` times `2^-53`, a number in `[0, 1)`. `chance(p)` is `float() < p`, so `chance(0.0)` is never true and `chance(1.0)` always is.

Tests: [std/random.lt](../conformance/std/random.lt), [std/random_below_panic.lt](../conformance/std/random_below_panic.lt), [std/random_range_panic.lt](../conformance/std/random_range_panic.lt).

<a id="std.shuffling"></a>
`shuffle(inout xs)` puts the elements of `xs` in a random order, every one equally likely, by Fisher and Yates's shuffle. For each index `i` from the last down to 1, it swaps element `i` with element `below(i + 1)`. `shuffled(xs)` gives the elements in the order that `shuffle` would put them in, drawing what it draws. `pick(xs)` gives element `below(len)`, or `None` for an empty list, which draws nothing.

Tests: [std/random.lt](../conformance/std/random.lt), [std/random_shuffle.lt](../conformance/std/random_shuffle.lt).

## Collections

<a id="std.deque"></a>
`std.collections` declares `pub type Deque<T> = { head: List<T>, tail: List<T> }`, a double-ended queue written in Stilt. Its elements are those of `head` in reverse order, then those of `tail`. Its functions, in `impl<T> Deque<T>`, are `Deque.new()`, `Deque.from_list(xs)`, `len`, `is_empty`, `push_front`, `push_back`, `pop_front`, `pop_back`, `front`, `back` and `to_list`. `Deque.from_list(xs)` puts the first element at the front, and `to_list` gives the elements from the front. When an end needs an element and its list is empty, half of the other list's elements move to it. So a sequence of `n` operations takes time proportional to `n`. Its `Eq`, `Ord`, `Hash` and `Show` impls work on `to_list()`, so two deques with the same elements in the same order are equal however they were built. Its `Eq` compares the two lists by `==`, so two deques of `[NaN]` aren't equal, and a deque of `[0.0]` is equal to one of `[-0.0]`.

Tests: [ported/josephus.lt](../conformance/ported/josephus.lt), [std/collections.lt](../conformance/std/collections.lt), [std/heap_and_deque_equality.lt](../conformance/std/heap_and_deque_equality.lt).

Checked by: for the costs, which no conformance test observes, the benchmark suite `bench`, which can measure them.

<a id="std.heap"></a>
`std.collections` declares `pub type Heap<T> = { items: List<T> }`, a priority queue written in Stilt whose `pop` gives the smallest element first. It is a binary heap: element `i` of `items` is no greater than elements `2i + 1` and `2i + 2`. Its functions, in `impl<T: Ord> Heap<T>`, are `Heap.new()`, `Heap.from_list(xs)`, `len`, `is_empty`, `push`, `pop`, `peek`, and `to_list`, which gives the elements in ascending order. `push` and `pop` take logarithmic time. A heap built from a record literal whose `items` break the heap's order behaves as the source does with those items. Its `Eq`, `Ord`, `Hash` and `Show` impls work on `to_list()`, so two heaps with the same elements are equal. Its `Eq` compares the two lists by `Ord.compare`, since `T` has `Ord`, where a deque's compares them by `==` ([std.deque](#std.deque)): two heaps of `[NaN]` are equal, and a heap of `[0.0]` isn't equal to one of `[-0.0]` ([traits.floats](11-traits.md#traits.floats)).

Tests: [ported/hamming_numbers.lt](../conformance/ported/hamming_numbers.lt), [std/collections.lt](../conformance/std/collections.lt), [std/heap_and_deque_equality.lt](../conformance/std/heap_and_deque_equality.lt).

Checked by: for the costs, the benchmark suite `bench`, which can measure them.

## Encodings and hashes

<a id="std.encoding"></a>
`std.encoding` writes bytes as text and reads them back. It is written in Stilt on the methods of `str` and `List`, and none of its functions performs anything or panics. `to_base64(bytes)` writes bytes in RFC 4648's base64. Each three bytes become four characters of `A` to `Z`, `a` to `z`, `0` to `9`, `+` and `/`, and the last group is padded with `=` to four. `to_base64_url(bytes)` writes them in RFC 4648's base64 for URLs, with `-` and `_` in place of `+` and `/`, and no padding. `from_base64(text)` and `from_base64_url(text)` give the bytes that such text writes. They are `None` for text that the matching writer can't write, except for the bits that its last character holds beyond the last byte, which they ignore. `from_base64` takes only a multiple of four characters, with at most two `=` at its end. `from_base64_url` takes no `=`, and no number of characters that leaves one over a multiple of four. `to_hex(bytes)` writes each byte as two lowercase hexadecimal digits. `from_hex(text)` reads two digits of either case for each byte, and is `None` for any other text.

Tests: [encoding/base64.lt](../conformance/encoding/base64.lt), [encoding/hex.lt](../conformance/encoding/hex.lt).

<a id="std.utf8-errors"></a>
`std.encoding` declares `pub type Utf8Error = | Invalid(offset: i64) | Truncated(offset: i64)`. `encoding.from_utf8(bytes)` gives the text whose UTF-8 is `bytes`. It raises at the first sequence that isn't well-formed in the Unicode Standard's table of well-formed UTF-8 (§3.9):

- `Truncated(i)` when the bytes end after the first bytes of a sequence that starts at offset `i`, which the bytes that follow could make whole;
- `Invalid(i)` otherwise.

So overlong forms, surrogates and values above `0x10FFFF` are `Invalid` at their first byte. `str.from_utf8` is `Some` exactly when `from_utf8` raises nothing.

Tests: [encoding/utf8.lt](../conformance/encoding/utf8.lt).

<a id="std.hashing"></a>
`std.hashing` is written in Stilt and performs nothing. `sha256(bytes)` is the SHA-256 hash of FIPS 180-4, 32 bytes. `hmac_sha256(key, message)` is the HMAC of RFC 2104 with SHA-256, 32 bytes, whose key is hashed first when it is longer than 64 bytes. `fnv1a(bytes)` is the 64-bit FNV-1a hash, a `u64`. It starts from `0xcbf29ce484222325`, and for each byte combines it with `^` and multiplies by `0x100000001b3`, wrapping.

Tests: [encoding/hashes.lt](../conformance/encoding/hashes.lt).

## Regular expressions

<a id="std.regex"></a>
`std.regex` is written in Stilt on the methods of `str` and `List`, and none of its functions performs anything or panics. It declares `pub type Regex = { source: str, groups: i64, program: List<Op> }`, a compiled pattern. Its fields are its source, the number of its capturing groups, and the instructions that match it, the variants of `Op`, which only the module reads. `regex.compile(source)` gives the `Regex` of a pattern. At the first mistake from the left, it raises `pub type Error = | Unexpected(offset: i64) | Unclosed(offset: i64) | Escape(offset: i64) | Order(offset: i64) | TooLarge`. Each offset counts the bytes of `source` before the character that it names, as [std.regex-syntax](#std.regex-syntax) gives them. A search runs the instructions over the text's scalar values, with at most one thread of matching for each instruction, and never goes back over the text. So its time is at most proportional to the text's length times the number of instructions, whatever the pattern and the text hold.

Tests: [regex/errors.lt](../conformance/regex/errors.lt), [regex/matching.lt](../conformance/regex/matching.lt).

<a id="std.regex-syntax"></a>
A pattern is alternatives separated by `|`. Each alternative is a sequence of items, possibly empty, and each item is an atom with at most one quantifier after it. An atom is one of these:

- a character other than `\`, `.`, `+`, `*`, `?`, `(`, `)`, `|`, `[`, `{`, `^` and `$`, which matches itself, so a `]` or a `}` alone does;
- `.`, which matches any scalar value but a line feed;
- `^`, which matches only at the start of the text, and `$`, which matches only at its end;
- an escape, a group or a class.

An **escape** is one of these:

- `\d`, which matches an ASCII digit;
- `\w`, which matches an ASCII letter or digit or `_`;
- `\s`, which matches one of U+0009 to U+000D and the space;
- `\D`, `\W` and `\S`, which match any other scalar value;
- `\n`, `\t` and `\r`, which match a line feed, a tab and a carriage return;
- `\b`, which matches between a scalar value that `\w` matches and one that it doesn't, the start and the end of the text counting as neither;
- `\B`, which matches wherever `\b` doesn't;
- `\` before any other printable ASCII character that is neither a letter nor a digit, which matches that character.

Any other escape, and a `\` that ends the pattern, are `Escape` at the `\`.

A **group** is `(` alternatives `)`, a capturing group, or `(?:` alternatives `)`, which captures nothing. Capturing groups are numbered from 1 in the order of their `(`s. A `(` that no `)` closes is `Unclosed` at the `(`, and a `)` that closes nothing is `Unexpected` at it. The 251st group open at once is `TooLarge`.

A **class** is `[`, an optional `^`, items, and `]`. It matches a scalar value that one of its items matches, or, after `^`, that none does. An item is a character, an escape that matches a class or one character, or a range `a-b` of two characters, which matches the scalar values from `a` to `b`. A `]` that comes first, after the optional `^`, is an item, and so is a `-` first or last. A range whose end is a `\` is `Escape` there, and one whose end comes before its start is `Order` at its start. `\b` and `\B` are `Escape` in a class. A `[` that no `]` closes is `Unclosed` at the `[`.

A quantifier repeats its atom:

- `*` any number of times, `+` at least once and `?` at most once;
- `{n}` `n` times, `{n,}` at least `n` times and `{n,m}` from `n` to `m` times, with `n` and `m` written in decimal.

A count above 1,000, or whose `m` is below its `n`, is `Order` at the `{`. A count that ends the pattern before its `}` is `Unclosed` at the `{`. Any other character where a count expects a digit, a `,` or a `}` is `Unexpected` there. A quantifier is **greedy**, preferring more repetitions, unless a `?` follows it, which makes it **lazy**, preferring fewer. A quantifier that follows no atom, at the start of a sequence, or another quantifier is `Unexpected` at it.

Once a pattern parses, it is `TooLarge` when its size is above 100,000. Sizes are these:

- a character, `.`, an escape, a class and an assertion have size 1;
- a sequence has the sum of its items' sizes;
- alternatives have the sum of their sizes plus twice their number;
- a group has its content's size plus 2;
- an atom of size `s` with a quantifier has size `(s + 1) × k + 1`. Here `k` is the quantifier's upper bound, or its lower bound plus 1 when it has none.

Tests: [regex/errors.lt](../conformance/regex/errors.lt), [regex/matching.lt](../conformance/regex/matching.lt).

<a id="std.regex-matching"></a>
A **match** of a pattern in a text starts and ends at boundaries of scalar values. It is given as `pub type Match = { start: i64, end: i64, text: str }`, its offsets in bytes and its text. Of the matches that start at the leftmost position where any starts, the one found is the first in the order in which the pattern prefers its choices. The pattern prefers an alternative over those after it, a greedy quantifier's next repetition over stopping, and a lazy quantifier's stopping over its next repetition. A repetition that matched nothing ends its quantifier.

`re.is_match(text)` is whether a match exists, and `re.find(text)` is the match found. `re.captures(text)` gives its groups: the match itself, then each capturing group in order. A group holds the part of the text that its last repetition in the match matched, or `None` when it took no part. `re.find_all(text)` gives the matches from left to right. Each search starts where the last match ended. An empty match that starts where the last one ended is left out, and the search goes on from the next scalar value.

Tests: [regex/groups.lt](../conformance/regex/groups.lt), [regex/matching.lt](../conformance/regex/matching.lt).

<a id="std.regex-replacing"></a>
`re.replace(text, to)` replaces each match of `find_all` by `to`. In `to`, these stand for other text:

- `$n`, with `n` written in decimal, stands for the text of group `n`, and for `""` when the group took no part or the pattern has no such group;
- `$$` stands for one `$`;
- any other `$` stands for itself.

`re.replace_first(text, to)` replaces only the match of `find`. `re.split(text)` gives the parts of the text before the first match of `find_all`, between each two, and after the last. So a text without a match gives itself alone, and an empty match at either end gives an empty part. `regex.escape(text)` puts a `\` before each of `\`, `.`, `+`, `*`, `?`, `(`, `)`, `|`, `[`, `]`, `{`, `}`, `^` and `$`. The pattern it gives matches exactly `text`.

Tests: [regex/errors.lt](../conformance/regex/errors.lt), [regex/groups.lt](../conformance/regex/groups.lt).

## JSON

<a id="std.json"></a>
The module `std.json` is written in Stilt on `std.meta` alone. It declares these types and traits:

- `pub type Value = | Null | Bool(bool) | Number(str) | Text(str) | Array(List<Value>) | Object(List<(str, Value)>)`, a JSON value whose numbers keep their text and whose objects keep their members in order;
- `pub type Error = | Syntax(line: i64, column: i64) | Missing(path: str) | Mismatch(path: str, expected: str, found: str)`, why text or a value isn't a value of the type asked for;
- `pub trait ToJson { fn to_json(self) -> Value }` and `pub trait FromJson { fn from_json(v: Value) -> Self / raise<Error> }`, a type's own JSON.

Its functions are these:

- `to_value<T>(value: T) -> Value` and `to_text<T>(value: T) -> str` ([std.json-writing](#std.json-writing));
- `from_value<T>(v: Value) -> T / raise<Error>` and `from_text<T>(text: str) -> T / raise<Error>` ([std.json-reading](#std.json-reading));
- `parse(text: str) -> Value / raise<Error>` ([std.json-parsing](#std.json-parsing));
- `render(v: Value) -> str` ([std.json-rendering](#std.json-rendering)).

Each of the four functions over `T` reflects on the parts of `T` ([meta.reflects](16-meta.md#meta.reflects)). The writers are guarded by `ToJson`, and the readers by `FromJson`. A type with a part that has no shape and no impl of the guard is E0350, *type without a shape given to a function that reflects*. It is reported at the call ([meta.types-without-shape](16-meta.md#meta.types-without-shape)). `std.json` is in the meta tier, and a module that only calls its functions stays in its tier ([meta.reflection-tier](16-meta.md#meta.reflection-tier)).

Tests: [json/parsing.lt](../conformance/json/parsing.lt), [json/reading.lt](../conformance/json/reading.lt), [json/reflection_errors.lt](../conformance/json/reflection_errors.lt), [json/rendering.lt](../conformance/json/rendering.lt), [json/writing.lt](../conformance/json/writing.lt).

<a id="std.json-writing"></a>
`to_value(value)` is `value.to_json()` when `T: ToJson` ([meta.bound-tests](16-meta.md#meta.bound-tests)), and otherwise follows `T`'s shape ([meta.shapes](16-meta.md#meta.shapes)):

| Shape | JSON |
| --- | --- |
| `Int` | A number, its decimal text |
| `Float` | A number, its text as [numbers.printing-floats](06-numbers.md#numbers.printing-floats) prints it; a NaN or an infinity panics with the kind `explicit`, whose message names the path to it |
| `Bool`, `Str` | `true` or `false`; a string |
| `Unit` | `null` |
| `Option` | `null` for `None`, and the JSON of `x` for `Some(x)` |
| `List`, `Set`, `Array`, `Tuple` | An array of its elements' JSON, in order |
| `Map` | An object, its entries as members in insertion order, when its key type's shape is `Str`, and otherwise an array of `[key, value]` arrays |
| `Record` | An object with a member per field, in the order of its shape, named by the field |
| `Variants` | `"Name"` for a variant without a payload, and `{"Name": [payload…]}` for one with a payload, as an array |

`to_text(value)` is `render(to_value(value))`.

Tests: [json/writing.lt](../conformance/json/writing.lt), [json/writing_infinity.lt](../conformance/json/writing_infinity.lt), [json/writing_nan.lt](../conformance/json/writing_nan.lt).

<a id="std.json-reading"></a>
`from_value(v)` is `T.from_json(v)` when `T: FromJson`. Otherwise, it reads the JSON that [std.json-writing](#std.json-writing) writes. So `from_value(to_value(x))` equals `x` for every value `x` whose type has no `ToJson` or `FromJson` impl at any depth, with two exceptions. A `Some(y)` whose `y` writes `null`, as `Some(None)` and `Some(())`, reads as `None`. A map with a default reads without one. Reading also follows these rules:

- an integer reads from a number whose text is an integer of its type's range, with no fraction and no exponent;
- a float reads from any number, as `str.to_f64` reads it, rounded to `f32` for an `f32`;
- an object's members that no field names are ignored, and of two members with one name, the last is read;
- a record's field of type `Option<U>` that no member names reads as `None`;
- a variant without a payload reads from a string that names it;
- a variant with a payload reads from an object with exactly one member, which names the variant and holds an array of its payload's length;
- a list and a set read from an array, a set keeping the first of equal elements;
- an array and a tuple read from an array of exactly their length;
- a map whose key type's shape is `Str` reads only from an object, and any other map only from an array of `[key, value]` arrays;
- of equal keys of a map, the last value is kept, at the position of the first.

`from_text(text)` is `from_value(parse(text))`.

Tests: [json/reading.lt](../conformance/json/reading.lt).

<a id="std.json-read-errors"></a>
A record's field of a type other than `Option` that no member names raises `Missing(path)`, with the path of the field, as `$.users[0].name`. Anything else that doesn't fit raises `Mismatch(path, expected, found)`, at the first mismatch in the order the value is read:

- `path` is where in `v` the mismatch was found: `$` for the root, followed by `.name` for a member and `[i]` for an element, as `$.roles[1]`;
- `expected` is the name of the type expected there, as `T.name()` gives it ([meta.shape-and-name](16-meta.md#meta.shape-and-name));
- `found` is the JSON found there, rendered and cut to its first 40 characters.

Tests: [json/reading.lt](../conformance/json/reading.lt).

<a id="std.json-parsing"></a>
`parse(text)` reads one JSON value as RFC 8259 defines it, with whitespace before and after it. It raises `Syntax(line, column)` at the first character that no JSON value can continue with, or at the end of the text. Lines and columns count from 1, columns in Unicode scalar values, and a line ends at each U+000A. A string's `\u` escapes of a surrogate pair make one character. A lone surrogate is a syntax error at the first character that shows it is one. For a low surrogate, that is the second hexadecimal digit of its escape, as the `C` of `\uDC00`. For a high surrogate, it is the first character after its escape that can't continue the escape of a low one. A value nested more than 512 arrays and objects deep is a syntax error at the bracket that opens the 513th.

Tests: [json/parsing.lt](../conformance/json/parsing.lt).

<a id="std.json-rendering"></a>
`render(v)` writes `v` with no whitespace. A string is written between `"`, as follows:

- `"` and `\` are escaped by `\`;
- U+0008, U+0009, U+000A, U+000C and U+000D are written `\b`, `\t`, `\n`, `\f` and `\r`;
- the other characters below U+0020 are written `\u` and four lowercase hexadecimal digits;
- every other character is written as itself.

A `Number` is written as its text, which `render` doesn't check.

Tests: [json/rendering.lt](../conformance/json/rendering.lt), [json/writing.lt](../conformance/json/writing.lt).

<a id="std.json-effects"></a>
No function of `std.json` performs anything but the raises its row declares. `from_value`, `from_text`, `parse` and `FromJson.from_json` may raise `json.Error`. Every function may panic and allocate.

Tests: [json/parsing.lt](../conformance/json/parsing.lt), [json/reading.lt](../conformance/json/reading.lt), [json/writing_nan.lt](../conformance/json/writing_nan.lt).

## The library's own tests

<a id="std.examples"></a>
Every `pub` function and method of the library has at least one `/// ex:` example ([program.doc-comments](04-programs.md#program.doc-comments)) that evaluates to `true`, except these:

- those whose declared row holds `io`;
- those that return `Never`;
- those of the numeric types other than `i64` and `f64`, which repeat the methods of `i64` and `f64` at another width;
- those of `std.meta` that take a value that only a macro's run makes ([macros.tokens-and-code](16-meta.md#macros.tokens-and-code)).

These examples are the library's own tests. `stilt test` runs the tests, examples and properties of the program's own modules only, never the library's, as it never runs a dependency's ([packages.no-build-time-code](04-programs.md#packages.no-build-time-code)).

Tests: [std/examples_are_the_program_s_own.lt](../conformance/std/examples_are_the_program_s_own.lt).

Checked by: each implementation's own tests, which run the library's examples, `test --std` in `interpreter/test/dune` and `compiler/stilt-cli/tests/std_examples.rs`, which also checks that every function the paragraph names has one.
