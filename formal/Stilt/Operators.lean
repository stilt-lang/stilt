/-!
# Operators

The kinds of the built-in operations' operators: arithmetic, shifts and bitwise
operators, comparisons, the searches of strings, the functions of lists, maps
and sets, the kinds of panic, the methods of the integer types, the
alignments of format specs, and the operations on the world. `Stilt.Syntax` names them in its operations.
-/

namespace Stilt

/-- The arithmetic operators `+`, `-`, `*`, `/` and `%` (numbers.integer-panics,
numbers.division-and-remainder and numbers.ieee-754). -/
inductive Arith where
  | add | sub | mul | div | rem
  deriving DecidableEq, Repr

/-- The native methods of `f32` and `f64`, the operations IEEE 754 defines exactly
(std.floats): `sqrt`, `floor`, `ceil`, `trunc`, `abs`, `round`, `min`, `max` and
`is_nan`. -/
inductive FloatMethod where
  | sqrt | floor | ceil | trunc | abs | round | min | max | isNan
  deriving DecidableEq, Repr

/-- Whether a float method takes a second operand: `min` and `max`. -/
def FloatMethod.binary : FloatMethod → Bool
  | .min | .max => true
  | _ => false

/-- The wrapping operators `+%`, `-%` and `*%` (numbers.wrapping). -/
inductive Wrapping where
  | add | sub | mul
  deriving DecidableEq, Repr

/-- The shifts `<<` and `>>` (numbers.shifts). -/
inductive Shift where
  | left | right
  deriving DecidableEq, Repr

/-- The bitwise operators `&`, `|` and `^` (numbers.bitwise-operators). -/
inductive Bitwise where
  | and | or | xor
  deriving DecidableEq, Repr

/-- The comparisons `==`, `!=`, `<`, `<=`, `>` and `>=` (numbers.comparisons). -/
inductive Cmp where
  | eq | ne | lt | le | gt | ge
  deriving DecidableEq, Repr

/-- The operations of `checked_add`, `checked_sub` and `checked_mul` (std.integers). -/
inductive Checked where
  | add | sub | mul
  deriving DecidableEq, Repr

/-- The exact result of a checked operation. -/
def Checked.exact : Checked → Int → Int → Int
  | .add, a, b => a + b
  | .sub, a, b => a - b
  | .mul, a, b => a * b

/-- The classes of a string's bytes: `is_ascii()`, and `is_ascii_digit()`,
`is_ascii_alpha()`, `is_ascii_alphanumeric()`, `is_ascii_whitespace()`,
`is_ascii_upper()` and `is_ascii_lower()` (std.str-classes). -/
inductive StrClass where
  | ascii | digit | alpha | alnum | whitespace | upper | lower
  deriving DecidableEq, Repr

/-- The tests for a substring: `contains`, `starts_with` and `ends_with`
(std.str-search). -/
inductive Search where
  | contains | startsWith | endsWith
  deriving DecidableEq, Repr

/-- The functions of lists that the calculus has: `xs.len()`, `xs.is_empty()`,
the list that `xs.push(x)` stores, `xs` with `x` after its last element
(std.lists), the integers a range yields, `a..b` or, `inclusive`, `a..=b`,
as the list a `for` over it iterates (expressions.range-iteration),
`sep.join(parts)`, the separator first (std.str), `xs.slice(a, b)`, and the
lists that `xs.insert(i, x)` and `xs.remove(i)` store (std.lists), and the
lists of strings that `s.chars()`, `s.split(sep)`, `s.lines()` and
`s.split_whitespace()` give (std.str and std.str-splitting). -/
inductive ListOp where
  | len | isEmpty | push
  | range (inclusive : Bool)
  | join
  | slice | insert | removeAt
  | chars | split | lines | splitWhitespace
  /-- `s.bytes()`, a string's UTF-8 bytes as `u8`s, and `s.code_points()`, its
  scalar values as `u32`s (std.bytes-and-scalars). -/
  | bytes | codePoints
  /-- The line that `io.read_line()` reads from the input, none at its end
  (std.read-line). -/
  | nextLine
  /-- `s.find(sub)`, or `s.rfind(sub)` when `last`: the byte offset of the first or
  the last occurrence, as a list of none or one (std.str-search). -/
  | find (last : Bool)
  /-- `str.from_utf8(bytes)` as a list of none or one string, or when `lossy`
  `str.from_utf8_lossy(bytes)` (std.code-points). -/
  | fromUtf8 (lossy : Bool)
  /-- `str.from_code_point(p)` as a list of none or one string (std.code-points). -/
  | fromCodePoint
  /-- `x.checked_add(y)`, `checked_sub` and `checked_mul` at the integer type of
  these bounds, as a list of none or one integer (std.integers). -/
  | checked (op : Checked) (lo hi : Int)
  /-- `x.to_T()` to the integer type of these bounds, which doesn't hold every value
  of `x`'s, as a list of none or one integer (numbers.conversions). -/
  | narrow (lo hi : Int)
  /-- `x.to_T()` from a float to the integer type of these bounds: its value
  truncated toward zero, as a list of none or one integer, none for NaN, the
  infinities and a truncation out of range (numbers.conversions). -/
  | truncate (lo hi : Int)
  deriving DecidableEq, Repr

/-- The functions of maps that the model holds: `Map.new()`,
`Map.with_default(d)`, `m.len()`, `m.is_empty()`, `m.contains(k)`, `m[k]` as a
value, `m.get_or(k, d)`, `m.keys()`, `m.values()` and `m.entries()`, and the map
that `m.insert(k, v)` and `m[k] = v` store and the one that `m.remove(k)`
stores (std.maps and std.map-functions). -/
inductive MapOp where
  | new | withDefault | len | isEmpty | contains | index | getOr | insert | remove
  | keys | values | entries
  /-- `==` on maps whose values have a key type, so that each value's `eq` is the
  built-in one (traits.structural-impls). -/
  | equal
  deriving DecidableEq, Repr

/-- The functions of two sets that give a set: `union`, `intersection`,
`difference` and `symmetric_difference` (std.sets). -/
inductive SetCombine where
  | union | intersection | difference | symmetricDifference
  deriving DecidableEq, Repr

/-- The tests of two sets: `is_subset`, `is_superset`, `is_disjoint`, and `==`
through the structural `Eq` of `Set` (std.sets and std.set-impls). -/
inductive SetRelation where
  | subset | superset | disjoint | equal
  deriving DecidableEq, Repr

/-- The functions of sets that the model holds: `Set.new()`,
`Set.from_list(xs)`, `s.len()`, `s.is_empty()`, `s.contains(x)`, `s.to_list()`,
the set that `s.insert(x)` and `s.remove(x)` store, and the functions of two
sets (std.sets). -/
inductive SetOp where
  | new | fromList | len | isEmpty | contains | insert | remove | toList
  | combine (op : SetCombine)
  | relate (op : SetRelation)
  deriving DecidableEq, Repr

/-- The natives of `str` from a string to a string: `trim()`, `trim_start()`
and `trim_end()` (std.str-splitting), `ascii_upper()`, `ascii_lower()` and
`reversed()` (std.str-building), and the input that a read of a line leaves
(std.read-line). -/
inductive StrMap where
  | trim | trimStart | trimEnd | asciiUpper | asciiLower | reversed | afterLine
  deriving DecidableEq, Repr

/-- The kinds of panic of the calculus (effects.panic-kinds): an index out of
bounds, in a list or a string, integer overflow, integer division by zero,
slicing a string inside a UTF-8 sequence, indexing a map without a default with
a missing key, `panic(msg)`, `unreachable()`, `unwrap` and `expect` of a `None`
or an `Err`, a false `assert`, a `when` on a value that a `when` holds
(shared.when-on-value-already-held), code with an error, reached, which the export
writes as this panic, and a typed hole, reached. -/
inductive PanicKind where
  | bounds
  | overflow
  | divideByZero
  | utf8Boundary
  | missingKey
  | explicit
  | unreachable
  | unwrap
  | assert
  | deadlock
  | checkError
  /-- A typed hole `?`, which the export writes as `Op.panic .hole` with no operands: the
  signature `Op.Sig.panic` gives it every type, so it takes the type its context expects
  (declarations.typed-holes), and a program with holes runs, a hole panicking with this
  kind only where it is reached (declarations.running-holes). -/
  | hole
  deriving DecidableEq, Repr

/-- The methods of the integer types that give an integer (std.integers):
`abs`, `min`, `max`, `saturating_add`, `saturating_sub`, `pow`, `div_euclid`,
`rem_euclid`, `gcd`, `lcm`, and the counts of bits, which give an `i64`. -/
inductive IntMethod where
  | abs | min | max | saturatingAdd | saturatingSub | pow | divEuclid | remEuclid | gcd | lcm
  | countOnes | leadingZeros | trailingZeros
  deriving DecidableEq, Repr

/-- A format spec's alignment (std.width-fill-and-alignment). -/
inductive Align where
  | left | center | right
  deriving DecidableEq, Repr

end Stilt
