import Stilt.Panics.Ops

/-!
# Operations that can't overflow

Which of the calculus's operations add the implicit effect `overflow`
(effects.overflow-effect): integer `+`, `-` and `*`, `-` on a value, `/` and `%` on a
signed type but by a divisor written as an integer literal other than `-1`, `<<` and `>>`
but by an amount written as an integer literal from 0 to one below the left operand's
width, `abs`, `pow`, `gcd` and `lcm`, and `div_euclid` and `rem_euclid` but by a divisor
written as an integer literal other than `0` and `-1` (`Op.overflowFreeOn`). The others
fit their type whenever their operands fit theirs, which a well-typed program's do
(`IntTy.within`), so `n / 2`, `x >> 1` and `a.min(b)` overflow on no run
(`Op.apply_quiet`). The model counts one more kind of site, which the Reference doesn't:
the lengths and counts that give an `i64`, `xs.len()` among them. The calculus's lists
have no greatest length (facts.greatest-length), so a length need not fit `i64`. Every
other operation, the wrapping operators, comparisons, bitwise operators and floats among
them, ends with its value or stuck whatever its operands. With `Op.panicFree`, an
operation that can't overflow can't panic at all (`Op.apply_serene`).
-/

namespace Stilt

/-- Whether a function of lists can't overflow: every one but `len` and `find`, which
give an `i64` (numbers.lengths-are-i64). -/
def ListOp.overflowFree : ListOp → Bool
  | .len | .find _ => false
  | _ => true

/-- Whether a function of maps can't overflow: every one but `len`. -/
def MapOp.overflowFree : MapOp → Bool
  | .len => false
  | _ => true

/-- Whether a function of sets can't overflow: every one but `len`. -/
def SetOp.overflowFree : SetOp → Bool
  | .len => false
  | _ => true

/-- Whether an operation can't overflow, whatever its operands: every one but integer
negation, arithmetic, shifts and methods, and those that give a length or a count as an
`i64`. -/
def Op.overflowFree : Op → Bool
  | .neg _ | .arith _ _ | .shift _ _ _ | .intMethod _ _ | .len | .charCount | .count => false
  | .list l => l.overflowFree
  | .map m => m.overflowFree
  | .set m => m.overflowFree
  | .panic k => k != .overflow
  | _ => true

/-- The methods of integer types whose result fits whenever their operands fit their
type: `min`, `max`, the saturating ones, and the counts of bits. -/
def IntMethod.bounded : IntMethod → Bool
  | .min | .max | .saturatingAdd | .saturatingSub | .countOnes | .leadingZeros
  | .trailingZeros => true
  | _ => false

/-- The integer that the second of two operands is written as, when it is an integer
literal: `n / 2`'s divisor, `x << 3`'s amount. A literal constant is its literal in the
calculus. -/
def literalOperand : List Expr → Option Int
  | [_, .int n] => some n
  | _ => none

/-- Whether an operation whose second operand is written as the literal `d`, if it is
one, adds no `overflow` (effects.overflow-effect): one that can't overflow whatever its
operands; `/` and `%` on an unsigned type, or by a literal other than `-1`; a shift by a
literal from 0 to one below the left operand's width (numbers.shift-amounts); `min`,
`max`, the saturating methods and the counts of bits; and `div_euclid` and `rem_euclid`
by a literal other than `0` and `-1` (std.integers). -/
def Op.overflowFreeBy : Op → Option Int → Bool
  | .arith .div k, d | .arith .rem k, d => !k.signed || (d.isSome && d != some (-1))
  | .shift _ k _, some b => decide (0 ≤ b ∧ b < k.bits)
  | .intMethod .divEuclid _, some b | .intMethod .remEuclid _, some b => b != 0 && b != -1
  | .intMethod m _, _ => m.bounded
  | o, _ => o.overflowFree

/-- Whether an operation on the operands `es` adds no `overflow` (effects.overflow-effect
and effects.without-overflow). -/
def Op.overflowFreeOn (o : Op) (es : List Expr) : Bool := o.overflowFreeBy (literalOperand es)

/-- An operation that can't overflow whatever its operands can't on any. -/
theorem Op.overflowFreeBy_of {o : Op} (h : o.overflowFree = true) (d : Option Int) :
    o.overflowFreeBy d = true := by
  unfold Op.overflowFreeBy
  split <;> simp_all [Op.overflowFree]

theorem ListOp.apply_serene {l : ListOp} (hl : l.panicFree = true) (hov : l.overflowFree = true)
    (vs : List Value) : Calm (l.apply vs) false := by
  unfold ListOp.apply
  split <;> first
    | (simp [ListOp.panicFree] at hl; done)
    | (simp [ListOp.overflowFree] at hov; done)
    | calm

theorem MapOp.apply_serene {m : MapOp} (hm : m.panicFree = true) (hov : m.overflowFree = true)
    (vs : List Value) : Calm (m.apply vs) false := by
  unfold MapOp.apply
  split <;> first
    | (simp [MapOp.panicFree] at hm; done)
    | (simp [MapOp.overflowFree] at hov; done)
    | calm

theorem SetOp.apply_serene {m : SetOp} (hov : m.overflowFree = true) (vs : List Value) :
    Calm (m.apply vs) false := by
  unfold SetOp.apply
  split <;> first | (simp [SetOp.overflowFree] at hov; done) | calm

theorem Op.compute_serene {o : Op} (ho : o.panicFree = true) (hov : o.overflowFree = true)
    (ss : List Scalar) : Calm (o.compute ss) false := by
  unfold Op.compute
  split <;> first
    | (simp [Op.panicFree] at ho; done)
    | (simp [Op.overflowFree] at hov; done)
    | calm

/-- An operation that can't panic, but by overflow, and can't overflow, can't panic. -/
theorem Op.apply_serene {o : Op} (ho : o.panicFree = true) (hov : o.overflowFree = true)
    (vs : List Value) : Calm (o.apply vs) false := by
  unfold Op.apply
  split
  · exact Calm.ok _
  · calm
  · simp [Op.panicFree] at ho
  · calm
  · calm
  · calm
  · exact ListOp.apply_serene (by simpa [Op.panicFree] using ho) (by simpa [Op.overflowFree] using hov) vs
  · exact MapOp.apply_serene (by simpa [Op.panicFree] using ho) (by simpa [Op.overflowFree] using hov) vs
  · exact SetOp.apply_serene (by simpa [Op.overflowFree] using hov) vs
  · simp [Op.panicFree] at ho
  · split
    · exact Calm.ok _
    · exact Calm.stuck
  · unfold Op.applyScalars
    split
    · exact Calm.map _ (Op.compute_serene ho hov _)
    · exact Calm.stuck

/-- An operation that can't panic, but by overflow, is calm where overflow is allowed, and
no panic at all where it can't overflow either. -/
theorem Op.apply_calmIn {o : Op} {ov : Bool} (ho : o.panicFree = true)
    (hov : (ov || o.overflowFree) = true) (vs : List Value) : Calm (o.apply vs) ov := by
  cases ov
  · exact (Op.apply_serene ho (by simpa using hov) vs).weaken
  · exact Op.apply_calm ho vs

end Stilt
