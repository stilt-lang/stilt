import Stilt.FloatText
import Stilt.Numbers

/-!
# Format specs

What a format spec does to a spliced value (lexical.format-specs): its width,
fill and alignment pad the value's shown text, measured in Unicode scalar values
(std.width-fill-and-alignment); a precision prints a float in fixed notation
with exactly that many fractional digits (std.precision); the kinds `x`, `X`,
`o` and `b` print an integer in another base, a negative one as its two's
complement (std.integer-kinds); and `e` prints a float in scientific notation
(std.scientific-notation). NaN and the infinities print as `nan`, `inf` and
`-inf` under every float spec (std.format-special-values). The digits of fixed
and scientific notation round the float's exact binary value half to even,
computed with natural numbers on its bits, as `Stilt.FloatText` computes its
shortest form.
-/

namespace Stilt

/-- `s` padded with copies of `fill` to at least `width` scalar values: before
it, after it, or around it with the odd copy after. -/
def padText (fill : Char) (align : Align) (width : Nat) (s : String) : String :=
  let pad := width - s.length
  let copies (n : Nat) := String.ofList (List.replicate n fill)
  match align with
  | .left => s ++ copies pad
  | .right => copies pad ++ s
  | .center => copies (pad / 2) ++ s ++ copies (pad - pad / 2)

/-- An integer of a type in a base, with no prefix and no leading zeros, a
negative one as its two's complement at its type's width, in uppercase when
`upper` says so (std.integer-kinds). -/
def IntTy.inBase (k : IntTy) (base : Nat) (upper : Bool) (n : Int) : String :=
  let digits := Nat.toDigits base (k.toBits n).toNat
  String.ofList (if upper then digits.map Char.toUpper else digits)

/-- `num / den` rounded half to even. -/
def roundHalfEven (num den : Nat) : Nat :=
  let q := num / den
  let r := num % den
  if 2 * r > den ∨ (2 * r = den ∧ q % 2 = 1) then q + 1 else q

/-- `m × 2^e × 10^p` rounded half to even. -/
def scaledRound (m : Nat) (e p : Int) : Nat :=
  roundHalfEven (m * 2 ^ e.toNat * 10 ^ p.toNat) (2 ^ (-e).toNat * 10 ^ (-p).toNat)

/-- The digits of `q`, with leading zeros to at least `n` of them. -/
def digitsAtLeast (n q : Nat) : String :=
  let d := toString q
  String.ofList (List.replicate (n - d.length) '0') ++ d

/-- `d₀.d₁…` from a string of digits: its first digit, then the others after a
point when there are any. -/
def pointAfterFirst (digits : String) : String :=
  let rest := digits.drop 1
  String.ofList (digits.toList.take 1) ++ (if rest.isEmpty then "" else "." ++ rest.toString)

namespace BinaryFormat

variable (F : BinaryFormat)

/-- Whether the float whose bits are `b` is negative, `-0.0` included. -/
def negative (b : Nat) : Bool := b / 2 ^ (F.bits + F.width) % 2 = 1

/-- The text of NaN and the infinities (std.format-special-values), or nothing
for a finite float. -/
def special (b : Nat) : Option String :=
  if b / 2 ^ F.bits % 2 ^ F.width = F.top then
    some (if b % 2 ^ F.bits ≠ 0 then "nan" else if F.negative b then "-inf" else "inf")
  else none

/-- A finite float's magnitude, `m × 2^e`, and whether the gap below it is half
the gap above, as at the bottom of a binade. -/
def magnitude (b : Nat) : Nat × Int × Bool :=
  let biased := b / 2 ^ F.bits % 2 ^ F.width
  let frac := b % 2 ^ F.bits
  if biased = 0 then (frac, F.minExp, false)
  else (frac + 2 ^ F.bits, (biased : Int) + F.minExp - 1, frac = 0 ∧ biased > 1)

/-- Fixed notation with `p` fractional digits, and no point when `p` is 0
(std.precision). -/
def fixed (p : Nat) (b : Nat) : String :=
  match F.special b with
  | some s => s
  | none =>
    let (m, e, _) := F.magnitude b
    let digits := digitsAtLeast (p + 1) (scaledRound m e p)
    let whole := digits.length - p
    (if F.negative b then "-" else "") ++ String.ofList (digits.toList.take whole) ++
      (if p = 0 then "" else "." ++ String.ofList (digits.toList.drop whole))

/-- Scientific notation: the shortest digits without a precision, and exactly
`p` digits after the point with one (std.scientific-notation). -/
def scientific (precision : Option Nat) (b : Nat) : String :=
  match F.special b with
  | some s => s
  | none =>
    let sign := if F.negative b then "-" else ""
    let (m, e, lower) := F.magnitude b
    if m = 0 then
      sign ++ "0" ++ (match precision with
        | some (p + 1) => "." ++ String.ofList (List.replicate (p + 1) '0')
        | _ => "") ++ "e0"
    else
      match precision with
      | none =>
        let (d, k) := F.shortest m e lower
        let digits := String.ofList ((toString d).toList.reverse.dropWhile (· = '0')).reverse
        sign ++ pointAfterFirst digits ++ "e" ++ toString (k - 1)
      | some p =>
        let E := FloatDigits.decimalExponent m e - 1
        let q := scaledRound m e (p - E)
        let (q, E) := if q = 10 ^ (p + 1) then (10 ^ p, E + 1) else (q, E)
        sign ++ pointAfterFirst (toString q) ++ "e" ++ toString E

end BinaryFormat

namespace FloatVal

/-- Fixed notation with `p` fractional digits (std.precision). -/
def fixed (p : Nat) : FloatVal → String
  | .f32 x => FloatTy.f32.format.fixed p x.toBits.toNat
  | .f64 x => FloatTy.f64.format.fixed p x.toBits.toNat

/-- Scientific notation (std.scientific-notation). -/
def scientific (precision : Option Nat) : FloatVal → String
  | .f32 x => FloatTy.f32.format.scientific precision x.toBits.toNat
  | .f64 x => FloatTy.f64.format.scientific precision x.toBits.toNat

end FloatVal

end Stilt
