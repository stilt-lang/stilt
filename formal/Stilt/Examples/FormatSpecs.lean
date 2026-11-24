import Stilt.FormatSpec

/-!
# Format specs

The outputs that std.width-fill-and-alignment, std.precision, std.integer-kinds and
std.scientific-notation give: `{7:*^4}` is `*7**`, `{255:x}` is `ff`, `{0:b}` is
`0`, `{-1:x}` at `i64` is sixteen `f`s, `{-0.001:.2}` is `-0.00`, `{12345.0:.2e}`
is `1.23e4` and `{0.0:.2e}` is `0.00e0`. A float is given by its bits, which the
kernel reduces, as Lean's own floats it doesn't.
-/

namespace Stilt.Examples.FormatSpecs

private def f64 : BinaryFormat := FloatTy.f64.format

example : padText '*' .center 4 "7" = "*7**" := by decide
example : IntTy.i64.inBase 16 false 255 = "ff" := by decide
example : IntTy.i64.inBase 2 false 0 = "0" := by decide
example : IntTy.i64.inBase 16 false (-1) = "ffffffffffffffff" := by decide

/-- `-0.001`, `12345.0` and `0.0` as binary64 bits. -/
example : f64.fixed 2 0xBF50624DD2F1A9FC = "-0.00" := by decide +kernel
example : f64.scientific (some 2) 0x40C81C8000000000 = "1.23e4" := by decide +kernel
example : f64.scientific (some 2) 0 = "0.00e0" := by decide +kernel
example : f64.scientific none 0 = "0e0" := by decide +kernel

end Stilt.Examples.FormatSpecs
