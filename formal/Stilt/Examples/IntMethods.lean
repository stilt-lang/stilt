import Stilt.Numbers

/-!
# Methods of the integer types

The cases that std.integers names: `x.pow(0)` is 1 for every `x`, 0
included, and `(-2).pow(63)` is `i64.MIN`; `abs` of `MIN` overflows;
`0.gcd(0)` is 0 and `i64.MIN.gcd(0)` overflows; `rem_euclid` is never
negative, and both Euclidean methods panic by 0 and overflow for `MIN` by `-1`;
the leading and trailing zeros of 0 are the width.
-/

namespace Stilt.Examples.IntMethods

private def i64 := IntTy.i64
private def overflow : Except Fault Int := .error (.panic .overflow)

example : i64.method .pow 0 0 = .ok 1 := by rfl
example : i64.method .pow (-2) 63 = .ok i64.min := by rfl
example : i64.method .pow 2 63 = overflow := by rfl
example : i64.method .abs i64.min 0 = overflow := by rfl
example : i64.method .gcd 0 0 = .ok 0 := by rfl
example : i64.method .gcd i64.min 0 = overflow := by rfl
example : i64.method .gcd (-12) 18 = .ok 6 := by rfl
example : i64.method .remEuclid (-7) 3 = .ok 2 := by rfl
example : i64.method .divEuclid (-7) 3 = .ok (-3) := by rfl
example : i64.method .remEuclid 7 0 = .error (.panic .divideByZero) := by rfl
example : IntTy.i16.method .remEuclid IntTy.i16.min (-1) = overflow := by rfl
example : i64.method .leadingZeros 0 0 = .ok 64 := by rfl
example : IntTy.u8.method .trailingZeros 0 0 = .ok 8 := by rfl
example : i64.method .countOnes (-1) 0 = .ok 64 := by rfl
example : IntTy.u8.method .saturatingAdd 250 10 = .ok 255 := by rfl

end Stilt.Examples.IntMethods
