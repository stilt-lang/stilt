import Stilt.Panics.Ops

/-!
# Operations that can't overflow

Which of the calculus's operations add the implicit effect `overflow`
(effects.overflow-effect): those that check that an integer fits its type. The calculus's
values carry no type, so an operation can't count on its operands fitting theirs: every
operation that checks a result's range is a site of `overflow` here, `n / 2` and
`xs.len()` among them, which the Reference counts as none, and every other one, the
wrapping operators, comparisons, bitwise operators and floats among them, ends with its
value or stuck whatever its operands. With `Op.panicFree`, such an operation can't panic
at all (`Op.apply_serene`).
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
  | _ => true

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
