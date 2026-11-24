import Stilt.Values

/-!
# Numbers

The ranges of the integer types, and what the arithmetic, wrapping, shift,
bitwise and comparison operators and the conversions compute
(numbers.numeric-types to numbers.wrapping-conversions).

An integer is the same value at every type that holds it, so an integer
operation computes with integers and checks that its type holds the result:
`+`, `-`, `*`, unary `-` and `/` panic with the kind `overflow` when it
doesn't, `/` and `%` with the kind `divide-by-zero` on a zero divisor, and `%`
with `overflow` where `/` would (numbers.integer-panics). The wrapping
operators, the shifts and the bitwise operators compute on the value's bits,
in two's complement, as Lean's `BitVec` does. Floats compute as Lean's
`Float32` and `Float` do, IEEE 754 binary32 and binary64 rounded to nearest
with ties to even (numbers.ieee-754).
-/

namespace Stilt

namespace IntTy

/-- The number of bits of an integer type (numbers.numeric-types). -/
def bits : IntTy → Nat
  | .i8 | .u8 => 8
  | .i16 | .u16 => 16
  | .i32 | .u32 => 32
  | .i64 | .u64 => 64

/-- Whether an integer type is signed (numbers.numeric-types). -/
def signed : IntTy → Bool
  | .i8 | .i16 | .i32 | .i64 => true
  | .u8 | .u16 | .u32 | .u64 => false

/-- The least integer of the type: −2ⁿ⁻¹ when it is signed, 0 otherwise
(numbers.numeric-types). -/
def min (k : IntTy) : Int := if k.signed then -2 ^ (k.bits - 1) else 0

/-- The greatest integer of the type: 2ⁿ⁻¹ − 1 when it is signed, 2ⁿ − 1
otherwise (numbers.numeric-types). -/
def max (k : IntTy) : Int := if k.signed then 2 ^ (k.bits - 1) - 1 else 2 ^ k.bits - 1

/-- The type holds the integer (numbers.numeric-types). -/
def Contains (k : IntTy) (n : Int) : Prop := k.min ≤ n ∧ n ≤ k.max

instance (k : IntTy) (n : Int) : Decidable (k.Contains n) := by
  unfold Contains
  infer_instance

/-- The bits of an integer, in two's complement. -/
def toBits (k : IntTy) (n : Int) : BitVec k.bits := BitVec.ofInt k.bits n

/-- The integer that bits of the type stand for: in two's complement when it
is signed. -/
def ofBits (k : IntTy) (x : BitVec k.bits) : Int := if k.signed then x.toInt else x.toNat

/-- The integer with the low bits of `n`, in two's complement (numbers.wrapping and
numbers.wrapping-conversions). -/
def wrap (k : IntTy) (n : Int) : Int := k.ofBits (k.toBits n)

/-- The integer, if the type holds it, or a panic of the kind `overflow`
(numbers.integer-panics). -/
def check (k : IntTy) (n : Int) : Except Fault Int :=
  if k.Contains n then .ok n else .error (.panic .overflow)

/-- `+`, `-`, `*`, `/` and `%`. `/` truncates toward zero and `%` has the sign
of the dividend (numbers.division-and-remainder); `MIN / -1` and `MIN % -1`
overflow (numbers.integer-panics). -/
def arith (k : IntTy) : Arith → Int → Int → Except Fault Int
  | .add, a, b => k.check (a + b)
  | .sub, a, b => k.check (a - b)
  | .mul, a, b => k.check (a * b)
  | .div, a, b => if b = 0 then .error (.panic .divideByZero) else k.check (a.tdiv b)
  | .rem, a, b =>
    if b = 0 then .error (.panic .divideByZero)
    else if k.Contains (a.tdiv b) then .ok (a.tmod b) else .error (.panic .overflow)

/-- `<<` discards the bits it shifts out, and `>>` is arithmetic on a signed
type and logical on an unsigned one (numbers.shifts). An amount that is negative,
or at least the type's width, overflows (numbers.shift-amounts). -/
def shift (k : IntTy) (o : Shift) (a b : Int) : Except Fault Int :=
  if b < 0 ∨ k.bits ≤ b then .error (.panic .overflow)
  else
    let x := k.toBits a
    .ok (k.ofBits (match o with
      | .left => x <<< b.toNat
      | .right => if k.signed then x.sshiftRight b.toNat else x >>> b.toNat))

theorem ofBits_contains (k : IntTy) (x : BitVec k.bits) : k.Contains (k.ofBits x) := by
  unfold Contains ofBits min max
  cases k.signed
  · have hx : (x.toNat : Int) < (2 : Int) ^ k.bits := by exact_mod_cast x.isLt
    simp only [Bool.false_eq_true, ↓reduceIte]
    omega
  · have := BitVec.le_toInt x
    have := BitVec.toInt_lt (x := x)
    simp only [↓reduceIte]
    omega

theorem min_le_zero (k : IntTy) : k.min ≤ 0 := by
  cases k <;> decide

theorem zero_le_max (k : IntTy) : 0 ≤ k.max := by
  cases k <;> decide

/-- The bits of an integer at its type's width, as a natural number. -/
def bitsOf (k : IntTy) (n : Int) : Nat := (k.toBits n).toNat

/-- `div_euclid` and `rem_euclid`'s result `r` of `a` by `b`: each panics with
`divide-by-zero` when `b` is 0, and with `overflow` for `MIN` by `-1`, whether
or not its own result fits (std.integers). -/
def euclid (k : IntTy) (a b r : Int) : Except Fault Int :=
  if b = 0 then .error (.panic .divideByZero)
  else if a = k.min ∧ b = -1 ∧ k.signed then .error (.panic .overflow)
  else k.check r

/-- What a method of an integer type computes, its result checked against the
type it gives: the operand's, or `i64` for a count of bits, so `abs`, `pow`,
`gcd` and `lcm` panic with `overflow` when the exact result doesn't fit, and
`div_euclid` and `rem_euclid` with `divide-by-zero` by 0 (std.integers). -/
def method (k : IntTy) : IntMethod → Int → Int → Except Fault Int
  | .abs, a, _ => k.check a.natAbs
  | .min, a, b => k.check (if a ≤ b then a else b)
  | .max, a, b => k.check (if a ≥ b then a else b)
  | .saturatingAdd, a, b => k.check (Max.max k.min (Min.min k.max (a + b)))
  | .saturatingSub, a, b => k.check (Max.max k.min (Min.min k.max (a - b)))
  | .pow, a, e =>
    if a.natAbs ≤ 1 then k.check (if a = -1 ∧ e % 2 = 1 then -1 else if a = 0 ∧ e ≠ 0 then 0 else
      if a = 0 then 1 else a.natAbs)
    else if e > 64 then .error (.panic .overflow)
    else k.check (a ^ e.toNat)
  | .divEuclid, a, b => k.euclid a b (a.ediv b)
  | .remEuclid, a, b => k.euclid a b (a.emod b)
  | .gcd, a, b => k.check (Int.gcd a b)
  | .lcm, a, b => k.check (Int.lcm a b)
  | .countOnes, a, _ => IntTy.i64.check ((List.range k.bits).countP (k.bitsOf a).testBit)
  | .leadingZeros, a, _ =>
    let n := k.bitsOf a
    IntTy.i64.check (if n = 0 then k.bits else k.bits - (Nat.log2 n + 1))
  | .trailingZeros, a, _ =>
    let n := k.bitsOf a
    IntTy.i64.check (((List.range k.bits).find? n.testBit).getD k.bits)

/-- The integer type a method's result has: `i64` for a count of bits, and
the operand's for the others. -/
def _root_.Stilt.IntMethod.result (k : IntTy) : IntMethod → IntTy
  | .countOnes | .leadingZeros | .trailingZeros => .i64
  | _ => k

/-- Whether a method takes a second operand, and of which type: the operand's,
or `u32` for `pow`'s exponent. -/
def _root_.Stilt.IntMethod.second (k : IntTy) : IntMethod → Option IntTy
  | .abs | .countOnes | .leadingZeros | .trailingZeros => none
  | .pow => some .u32
  | _ => some k

/-- The integer that a string of decimal digits, with a `-` before them for a
signed type, stands for, if the string is one and the type holds the integer:
leading zeros are accepted, and `+`, `_`, whitespace and radix prefixes aren't
(numbers.parsing). -/
def parse (k : IntTy) (s : String) : Option Int :=
  let digits (cs : List Char) : Option Nat :=
    if cs.isEmpty || !cs.all Char.isDigit then none
    else some (cs.foldl (fun n c => 10 * n + (c.toNat - '0'.toNat)) 0)
  let value := match s.toList with
    | '-' :: cs => if k.signed then (fun n : Nat => -(n : Int)) <$> digits cs else none
    | cs => (fun n : Nat => (n : Int)) <$> digits cs
  value.filter fun n => decide (k.Contains n)

/-- The integer a string parses as at the type, or 0 when it doesn't parse:
`s.to_k()` is `Some` of it exactly when it parses (numbers.parsing). -/
def parsedOrZero (k : IntTy) (s : String) : Int := (k.parse s).getD 0

theorem contains_parsedOrZero (k : IntTy) (s : String) : k.Contains (k.parsedOrZero s) := by
  unfold parsedOrZero
  cases h : k.parse s with
  | none => exact ⟨k.min_le_zero, k.zero_le_max⟩
  | some n =>
    unfold parse at h
    simpa using (Option.filter_eq_some_iff.1 h).2

/-- A remainder lies between zero and the dividend, so the dividend's type holds it. -/
theorem contains_tmod {k : IntTy} {a : Int} (ha : k.Contains a) (b : Int) : k.Contains (a.tmod b) := by
  have habs : (a.tmod b).natAbs ≤ a.natAbs := by
    rw [Int.natAbs_tmod]
    exact Nat.mod_le _ _
  have h0 := k.min_le_zero
  have h1 := k.zero_le_max
  obtain ⟨hlo, hhi⟩ := ha
  rcases Int.le_total 0 a with h | h
  · have := Int.tmod_nonneg b h
    constructor <;> omega
  · have hneg : a.tmod b = -((-a).tmod b) := by rw [Int.neg_tmod, Int.neg_neg]
    have := Int.tmod_nonneg b (Int.neg_nonneg_of_nonpos h)
    constructor <;> omega

end IntTy

/-- A comparison of two integers (numbers.comparisons). -/
def Cmp.ints : Cmp → Int → Int → Bool
  | .eq, a, b => a == b
  | .ne, a, b => a != b
  | .lt, a, b => decide (a < b)
  | .le, a, b => decide (a ≤ b)
  | .gt, a, b => decide (b < a)
  | .ge, a, b => decide (b ≤ a)

/-- `&`, `|` and `^`, bit by bit (numbers.bitwise-operators). -/
def Bitwise.bits {n : Nat} : Bitwise → BitVec n → BitVec n → BitVec n
  | .and, x, y => x &&& y
  | .or, x, y => x ||| y
  | .xor, x, y => x ^^^ y

/-- `+%`, `-%` and `*%`, on integers, before the result wraps (numbers.wrapping). -/
def Wrapping.ints : Wrapping → Int → Int → Int
  | .add, a, b => a + b
  | .sub, a, b => a - b
  | .mul, a, b => a * b

namespace FloatVal

/-- A float literal, `m × 10^±e`, rounded to the nearest value of its type
(numbers.float-literals). -/
def ofScientific : FloatTy → Nat → Bool → Nat → FloatVal
  | .f32, m, s, e => .f32 (OfScientific.ofScientific m s e)
  | .f64, m, s, e => .f64 (OfScientific.ofScientific m s e)

/-- An integer converted to a float type, rounded to nearest with ties to
even (numbers.conversions). -/
def ofInt : FloatTy → Int → FloatVal
  | .f32, n => .f32 (Float32.ofInt n)
  | .f64, n => .f64 (Float.ofInt n)

/-- A float converted to a float type: `f32` to `f64` exactly, `f64` to `f32`
rounded to nearest with ties to even, and a float to its own type unchanged
(numbers.conversions). -/
def convert : FloatVal → FloatTy → FloatVal
  | .f32 x, .f32 => .f32 x
  | .f32 x, .f64 => .f64 x.toFloat
  | .f64 x, .f32 => .f32 x.toFloat32
  | .f64 x, .f64 => .f64 x

/-- `-x` (numbers.ieee-754). -/
def neg : FloatVal → FloatVal
  | .f32 x => .f32 (-x)
  | .f64 x => .f64 (-x)

/-- `+`, `-`, `*` and `/` on two floats of the same type, rounded to that type
(numbers.ieee-754). `%` is `fmod`, which the model leaves out. -/
def arith : Arith → FloatVal → FloatVal → Option FloatVal
  | .add, .f32 x, .f32 y => some (.f32 (x + y))
  | .sub, .f32 x, .f32 y => some (.f32 (x - y))
  | .mul, .f32 x, .f32 y => some (.f32 (x * y))
  | .div, .f32 x, .f32 y => some (.f32 (x / y))
  | .add, .f64 x, .f64 y => some (.f64 (x + y))
  | .sub, .f64 x, .f64 y => some (.f64 (x - y))
  | .mul, .f64 x, .f64 y => some (.f64 (x * y))
  | .div, .f64 x, .f64 y => some (.f64 (x / y))
  | _, _, _ => none

/-- A comparison of two floats of the same type, as IEEE 754 compares them: NaN
is unequal to everything, itself included (numbers.ieee-754). -/
def compare : Cmp → FloatVal → FloatVal → Option Bool
  | .eq, .f32 x, .f32 y => some (x == y)
  | .ne, .f32 x, .f32 y => some (!(x == y))
  | .lt, .f32 x, .f32 y => some (decide (x < y))
  | .le, .f32 x, .f32 y => some (decide (x ≤ y))
  | .gt, .f32 x, .f32 y => some (decide (y < x))
  | .ge, .f32 x, .f32 y => some (decide (y ≤ x))
  | .eq, .f64 x, .f64 y => some (x == y)
  | .ne, .f64 x, .f64 y => some (!(x == y))
  | .lt, .f64 x, .f64 y => some (decide (x < y))
  | .le, .f64 x, .f64 y => some (decide (x ≤ y))
  | .gt, .f64 x, .f64 y => some (decide (y < x))
  | .ge, .f64 x, .f64 y => some (decide (y ≤ x))
  | _, _, _ => none

/-- A finite `f64` truncated toward zero, when its magnitude is below `2^64`, past
which no integer type reaches. -/
def truncInt (x : Float) : Option Int :=
  if x.isNaN || x.isInf then none
  else
    let t := if x < 0 then x.ceil else x.floor
    if 18446744073709551616.0 ≤ t.abs then none
    else if t < 0 then some (-((-t).toUInt64.toNat : Int)) else some (t.toUInt64.toNat : Int)

/-- A float truncated toward zero, none for NaN, the infinities and a magnitude of
`2^64` or more (numbers.conversions). An `f32` widens to `f64` exactly first. -/
def truncated : FloatVal → Option Int
  | .f32 x => truncInt x.toFloat
  | .f64 x => truncInt x

/-- Whether a float is NaN. -/
def isNaN : FloatVal → Bool
  | .f32 x => x.isNaN
  | .f64 x => x.isNaN

/-- Whether a float has its sign bit set, as `-0.0` has. -/
def signBit : FloatVal → Bool
  | .f32 x => x.toBits >>> 31 == 1
  | .f64 x => x.toBits >>> 63 == 1

/-- A one-operand native method: `sqrt`, `floor`, `ceil`, `abs`, `round`, which
rounds halves away from zero, and `trunc`, which rounds toward zero
(std.floats). -/
def unary (m : FloatMethod) : FloatVal → FloatVal
  | .f32 x => .f32 (match m with
    | .sqrt => x.sqrt | .floor => x.floor | .ceil => x.ceil | .abs => x.abs | .round => x.round
    | .trunc => if x < 0 then x.ceil else x.floor
    | _ => x)
  | .f64 x => .f64 (match m with
    | .sqrt => x.sqrt | .floor => x.floor | .ceil => x.ceil | .abs => x.abs | .round => x.round
    | .trunc => if x < 0 then x.ceil else x.floor
    | _ => x)

/-- `min` and `max` on two floats of the same type, IEEE 754-2019's `minimum` and
`maximum`: a NaN operand gives NaN, and `-0.0` is less than `0.0` (std.floats). -/
def extremum (least : Bool) (x y : FloatVal) : Option FloatVal :=
  if x.type ≠ y.type then none
  else if x.isNaN then some x
  else if y.isNaN then some y
  else match compare .lt x y, compare .lt y x with
    | some true, _ => some (if least then x else y)
    | _, some true => some (if least then y else x)
    | _, _ => some (if x.signBit == least then x else y)

theorem type_unary (m : FloatMethod) (x : FloatVal) : (x.unary m).type = x.type := by
  cases x <;> rfl

theorem extremum_some (least : Bool) {x y : FloatVal} (h : y.type = x.type) :
    ∃ z, extremum least x y = some z ∧ z.type = x.type := by
  unfold extremum
  simp only [h, ne_eq, not_true_eq_false, ↓reduceIte]
  split
  · exact ⟨x, rfl, rfl⟩
  · split
    · exact ⟨y, rfl, h⟩
    · split <;> (try split) <;> first | exact ⟨_, rfl, rfl⟩ | exact ⟨_, rfl, h⟩

theorem type_ofScientific (k : FloatTy) (m : Nat) (s : Bool) (e : Nat) :
    (ofScientific k m s e).type = k := by
  cases k <;> rfl

theorem type_ofInt (k : FloatTy) (n : Int) : (ofInt k n).type = k := by
  cases k <;> rfl

theorem type_convert (x : FloatVal) (k : FloatTy) : (x.convert k).type = k := by
  cases x <;> cases k <;> rfl

/-- Whether a float is an infinity. -/
def isInf : FloatVal → Bool
  | .f32 x => x.isInf
  | .f64 x => x.isInf

/-- The digits as a number. -/
def digitsValue (cs : List Char) : Nat := cs.foldl (fun n c => 10 * n + (c.toNat - '0'.toNat)) 0

/-- `m × 10^e` at the type, rounded to nearest with ties to even, with `-` when `neg`;
an exponent past every float's range is an overflow, or a zero, without computing
the power (numbers.parsing). -/
def ofDecimal (k : FloatTy) (neg : Bool) (m : Nat) (e : Int) : Option FloatVal :=
  let mag := (Nat.repr m).length + e
  let v := if m = 0 || mag < -400 then ofScientific k 0 false 0
    else if mag > 400 then ofScientific k 1 false 400
    else ofScientific k m (e < 0) e.natAbs
  let v := if neg then v.neg else v
  if v.isInf then none else some v

/-- The float a string stands for at the type, if it matches
`-?[0-9]+(\.[0-9]+)?([eE][+-]?[0-9]+)?` and its value, rounded to nearest with ties to
even, is finite (numbers.parsing). -/
def parse (k : FloatTy) (s : String) : Option FloatVal :=
  let digit := Char.isDigit
  let (neg, cs) := match s.toList with
    | '-' :: cs => (true, cs)
    | cs => (false, cs)
  let whole := cs.takeWhile digit
  let rest := cs.drop whole.length
  let (frac, rest, dotted) := match rest with
    | '.' :: r => (r.takeWhile digit, r.drop (r.takeWhile digit).length, true)
    | r => ([], r, false)
  let m := digitsValue (whole ++ frac)
  let finish (x : Int) := ofDecimal k neg m (x - frac.length)
  if whole.isEmpty || (dotted && frac.isEmpty) then none else
  match rest with
  | [] => finish 0
  | c :: r =>
    if c != 'e' && c != 'E' then none else
    let (eneg, ds) := match r with
      | '-' :: t => (true, t)
      | '+' :: t => (false, t)
      | t => (false, t)
    if ds.isEmpty || !ds.all digit then none
    else finish (if eneg then -(digitsValue ds : Int) else digitsValue ds)

/-- The float a string parses as at the type, or zero when it doesn't:
`s.to_f()` is `Some` of it exactly when it parses (numbers.parsing). -/
def parsedOrZero (k : FloatTy) (s : String) : FloatVal :=
  ((parse k s).getD (ofInt k 0)).convert k

theorem type_neg (x : FloatVal) : x.neg.type = x.type := by
  cases x <;> rfl

/-- Floats of one type give a float of that type, but for `%`. -/
theorem arith_some {o : Arith} (ho : o ≠ .rem) {x y : FloatVal} (h : y.type = x.type) :
    ∃ z, arith o x y = some z ∧ z.type = x.type := by
  cases x <;> cases y <;> cases o <;> first
    | exact absurd rfl ho
    | exact ⟨_, rfl, rfl⟩
    | simp [type] at h

theorem compare_some (c : Cmp) {x y : FloatVal} (h : y.type = x.type) :
    ∃ b, compare c x y = some b := by
  cases x <;> cases y <;> cases c <;> first
    | exact ⟨_, rfl⟩
    | simp [type] at h

end FloatVal

end Stilt
