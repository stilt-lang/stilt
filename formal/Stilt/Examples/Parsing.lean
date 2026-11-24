import Stilt.Numbers

/-!
# Parsing integers

The cases of numbers.parsing: leading zeros are accepted, so `"007"` parses as 7;
a `-` only for a signed type; and `+`, `_`, whitespace, an empty string and a
value out of the type's range are rejected.
-/

namespace Stilt.Examples.Parsing

example : IntTy.i64.parse "007" = some 7 := by decide
example : IntTy.i64.parse "-12" = some (-12) := by decide
example : IntTy.u8.parse "-1" = none := by decide
example : IntTy.u8.parse "256" = none := by decide
example : IntTy.i8.parse "-128" = some (-128) := by decide
example : IntTy.i64.parse "+1" = none := by decide
example : IntTy.i64.parse "1_000" = none := by decide
example : IntTy.i64.parse " 1" = none := by decide
example : IntTy.i64.parse "" = none := by decide
example : IntTy.i64.parse "-" = none := by decide

end Stilt.Examples.Parsing
