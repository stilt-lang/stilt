import Stilt.Values

/-!
# Printed floats

A float prints in the shortest form that reads back as the same value
(numbers.printing-floats, numbers.float-digits and numbers.float-notation). The
digits are computed exactly, with natural numbers, from the float's bits: they
are the shortest that lie inside the float's rounding interval, which holds
every real that rounds to it to nearest with ties to even (numbers.ieee-754),
and of two strings of that length, the one nearer the float's exact value.
-/

namespace Stilt

/-- A binary interchange format: the bits its significand stores and the
width of its exponent. -/
structure BinaryFormat where
  bits : Nat
  width : Nat

/-- binary32 and binary64 (numbers.ieee-754). -/
def FloatTy.format : FloatTy → BinaryFormat
  | .f32 => ⟨23, 8⟩
  | .f64 => ⟨52, 11⟩

/-- Compares `a × 10^p` with `b × 2^q`. -/
def compareScaled (a : Nat) (p : Int) (b : Nat) (q : Int) : Ordering :=
  compare (a * 10 ^ p.toNat * 2 ^ (-q).toNat) (b * 2 ^ q.toNat * 10 ^ (-p).toNat)

namespace FloatDigits

/-- Whether `c × 10^p` reads back as the float `m × 2^e`: it lies inside the
float's rounding interval, whose ends belong to it when `m` is even, and whose
lower half is half as wide when `lower` says so. -/
def readsBack (m : Nat) (e : Int) (lower : Bool) (c : Nat) (p : Int) : Bool :=
  let lo := 4 * m - (if lower then 1 else 2)
  let hi := 4 * m + 2
  let edge (o : Ordering) (inside : Ordering) := o = inside ∨ (o = .eq ∧ m % 2 = 0)
  edge (compareScaled c p lo (e - 2)) .gt && edge (compareScaled c p hi (e - 2)) .lt

/-- The least `k` with `m × 2^e < 10^k`. -/
def decimalExponent (m : Nat) (e : Int) : Int :=
  let est : Int := ((Nat.log2 m : Int) + e) * 30103 / 100000
  let k := [est - 1, est, est + 1, est + 2].find? fun k => compareScaled 1 k m e = .gt
  k.getD (est + 2)

/-- Of `d` and `d + 1` at `× 10^p`, those that read back, the one nearest
`m × 2^e`, and of two as near, the even one (numbers.float-digits). -/
def pick (m : Nat) (e : Int) (lower : Bool) (d : Nat) (p : Int) : Option Nat :=
  let exact := compareScaled d p m e = .eq
  match readsBack m e lower d p, !exact && readsBack m e lower (d + 1) p with
  | true, true =>
    match compareScaled (2 * d + 1) p (2 * m) e with
    | .gt => some d
    | .lt => some (d + 1)
    | .eq => some (if d % 2 = 0 then d else d + 1)
  | true, false => some d
  | false, true => some (d + 1)
  | false, false => none

end FloatDigits

namespace BinaryFormat

variable (F : BinaryFormat)

/-- The exponent's bias. -/
def bias : Nat := 2 ^ (F.width - 1) - 1

/-- The exponent of a significand's last bit in the subnormals. -/
def minExp : Int := 1 - (F.bias : Int) - F.bits

/-- The biased exponent of the infinities and NaNs. -/
def top : Nat := 2 ^ F.width - 1

/-- The shortest digits `d` and the exponent `k` with `0.d × 10^k` reading back
as the float `m × 2^e`, by digit counts from 1 up; `F.bits` digits always
suffice. -/
def shortest (m : Nat) (e : Int) (lower : Bool) : Nat × Int :=
  let k := FloatDigits.decimalExponent m e
  let found := (List.range (F.bits + 1)).findSome? fun i =>
    let p := k - (i + 1 : Nat)
    let d := (m * 2 ^ e.toNat * 10 ^ (-p).toNat) / (2 ^ (-e).toNat * 10 ^ p.toNat)
    (FloatDigits.pick m e lower d p).map fun c => if c = 10 ^ (i + 1) then (1, k + 1) else (c, k)
  found.getD (m, k)

end BinaryFormat

/-- `0.d × 10^k` in the notation of numbers.float-notation. -/
def floatNotation (d : Nat) (k : Int) : String :=
  let digits := (toString d).toList.reverse.dropWhile (· = '0') |>.reverse
  let n := digits.length
  let zeros (j : Nat) := List.replicate j '0'
  let text : List Char :=
    if -4 < k ∧ k ≤ 16 then
      if k ≤ 0 then ['0', '.'] ++ zeros (-k).toNat ++ digits
      else if n ≤ k.toNat then digits ++ zeros (k.toNat - n) ++ ['.', '0']
      else digits.take k.toNat ++ ['.'] ++ digits.drop k.toNat
    else
      let rest := digits.drop 1
      digits.take 1 ++ (if rest.isEmpty then [] else '.' :: rest) ++ 'e' :: (toString (k - 1)).toList
  String.ofList text

/-- The printed form of the float whose bits are `b` in the format `F`
(numbers.printing-floats). -/
def BinaryFormat.text (F : BinaryFormat) (b : Nat) : String :=
  let size := F.bits + F.width
  let sign := if b / 2 ^ size % 2 = 1 then "-" else ""
  let biased := b / 2 ^ F.bits % 2 ^ F.width
  let frac := b % 2 ^ F.bits
  if biased = F.top then (if frac = 0 then sign ++ "inf" else "nan")
  else if biased = 0 ∧ frac = 0 then sign ++ "0.0"
  else
    let (m, e, lower) :=
      if biased = 0 then (frac, F.minExp, false)
      else (frac + 2 ^ F.bits, (biased : Int) + F.minExp - 1, frac = 0 ∧ biased > 1)
    let (d, k) := F.shortest m e lower
    sign ++ floatNotation d k

namespace FloatVal

/-- A float's printed form (numbers.printing-floats). -/
def text : FloatVal → String
  | .f32 x => FloatTy.f32.format.text x.toBits.toNat
  | .f64 x => FloatTy.f64.format.text x.toBits.toNat

end FloatVal

end Stilt
