import Stilt.Numbers

/-!
# Strings

What the natives of `str` that the calculus holds compute: its length in
bytes, slicing between byte offsets, the tests for a substring, and the
order of strings by their bytes (std.bytes-and-scalars, std.str, std.str-search
and traits.built-in-impls).

A string is Lean's `String`, a sequence of Unicode scalar values, and works as
its list of characters, so that a proof by evaluation can run it. Its length
and offsets count the bytes of its UTF-8 encoding (std.bytes-and-scalars).
-/

namespace Stilt

namespace Str

/-- The byte offsets of the boundaries between scalar values, counting from
`i`: before each, and at the end. -/
def boundariesFrom : Nat → List Char → List Nat
  | i, [] => [i]
  | i, c :: cs => i :: boundariesFrom (i + c.utf8Size) cs

/-- The scalar values that lie between the byte offsets `a` and `b`, counting
from `i`. -/
def between : Nat → Nat → Nat → List Char → List Char
  | _, _, _, [] => []
  | i, a, b, c :: cs =>
    (if a ≤ i ∧ i + c.utf8Size ≤ b then [c] else []) ++ between (i + c.utf8Size) a b cs

/-- `s.slice(start, end)`: the bytes from `start` up to `end`. It panics with
`bounds` unless `0 ≤ start ≤ end ≤ len`, and otherwise with `utf8-boundary`
when an offset falls inside a UTF-8 sequence (std.str). -/
def slice (s : String) (a b : Int) : Except Fault String :=
  if ¬(0 ≤ a ∧ a ≤ b ∧ b ≤ s.utf8ByteSize) then .error (.panic .bounds)
  else if a.toNat ∈ boundariesFrom 0 s.toList ∧ b.toNat ∈ boundariesFrom 0 s.toList then
    .ok (String.ofList (between 0 a.toNat b.toNat s.toList))
  else .error (.panic .utf8Boundary)

/-- `s.len()`, the length in bytes, an `i64` (std.str and numbers.lengths-are-i64).
No string a machine holds is longer than `i64` counts; a longer one would
overflow. -/
def len (s : String) : Except Fault Int := IntTy.i64.check s.utf8ByteSize

end Str

/-- `contains(sub)`, `starts_with(prefix)` and `ends_with(suffix)`: whether the
second string is in the first, at its start, or at its end; every string
contains `""` (std.str-search). -/
def Search.test : Search → String → String → Bool
  | .contains, s, t => decide (t.toList <:+: s.toList)
  | .startsWith, s, t => decide (t.toList <+: s.toList)
  | .endsWith, s, t => decide (t.toList <:+ s.toList)

/-- A comparison of two strings, by their bytes, which is the same as by their
scalar values (traits.built-in-impls). -/
def Cmp.strs : Cmp → String → String → Bool
  | .eq, s, t => decide (s.toList = t.toList)
  | .ne, s, t => !decide (s.toList = t.toList)
  | .lt, s, t => decide (s.toList < t.toList)
  | .le, s, t => decide (s.toList ≤ t.toList)
  | .gt, s, t => decide (t.toList < s.toList)
  | .ge, s, t => decide (t.toList ≤ s.toList)

/-- A comparison of two Booleans, with `false < true` (traits.built-in-impls). -/
def Cmp.bools : Cmp → Bool → Bool → Bool
  | .eq, a, b => a == b
  | .ne, a, b => a != b
  | .lt, a, b => !a && b
  | .le, a, b => !a || b
  | .gt, a, b => a && !b
  | .ge, a, b => a || !b

end Stilt
