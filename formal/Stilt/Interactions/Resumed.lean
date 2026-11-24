/-!
# Operations take values

handlers.no-inout-parameter: an operation has no `inout` parameter. The model is a performance in a
store, whose handler's body adds to its copy of the argument before `resume`
and after it, and the rest of the `with`'s block, which `resume` runs, a
function of the store. Taking the argument by value, the body writes no place
of the store, so the store after the `with` is the block's (`values_untouched`).
With an `inout` parameter, writing in place would write the place after the
block, once the access had ended, which a copy written back at `resume` doesn't:
`inout_differ` shows the two stores apart, and `agree_without_later_writes`
that they agree exactly when the body writes nothing after `resume`.
-/

namespace Stilt.Interactions.Resumed

/-- A store, from places to values. -/
abbrev Store := Nat → Int

/-- `s` with the place `p` holding `v`. -/
def Store.set (s : Store) (p : Nat) (v : Int) : Store :=
  fun q => if q = p then v else s q

/-- A body that resumes once: what it adds to its argument before `resume` and
after it. -/
structure Body where
  before : Int
  after : Int

/-- handlers.no-inout-parameter: the argument, read from `p`, is a value: the body changes
its own copy, and the store goes on as the rest of the block leaves it. The
pair is the store after the `with` and the body's copy. -/
def byValue (b : Body) (p : Nat) (rest : Store → Store) (s : Store) :
    Store × Int :=
  (rest s, s p + b.before + b.after)

/-- handlers.resuming-keeps-exclusivity: a body given values writes no place of the code it
suspends, before `resume` or after it. -/
theorem values_untouched (b : Body) (p : Nat) (rest : Store → Store)
    (s : Store) : (byValue b p rest s).1 = rest s := rfl

/-- An `inout` parameter written in place: before `resume`, then the rest of
the block, then after it, when the access has ended. -/
def inPlace (b : Body) (p : Nat) (rest : Store → Store) (s : Store) : Store :=
  let s1 := s.set p (s p + b.before)
  let s2 := rest s1
  s2.set p (s2 p + b.after)

/-- An `inout` parameter copied in and written back at `resume`, when the
access ends: what the body writes after it reaches nothing. -/
def copiedAtResume (b : Body) (p : Nat) (rest : Store → Store) (s : Store) :
    Store :=
  rest (s.set p (s p + b.before))

/-- The program of handlers.no-inout-parameter, whose body adds 1, resumes and adds 100: the two
models of an `inout` parameter leave different stores. -/
theorem inout_differ :
    inPlace ⟨1, 100⟩ 0 id (fun _ => 1) 0 ≠ copiedAtResume ⟨1, 100⟩ 0 id (fun _ => 1) 0 := by
  simp [inPlace, copiedAtResume, Store.set]

/-- They agree when the body writes nothing after `resume`, which no body can
promise, since it may go on once the block ends. -/
theorem agree_without_later_writes (b : Body) (p : Nat) (rest : Store → Store)
    (s : Store) (h : b.after = 0) :
    inPlace b p rest s = copiedAtResume b p rest s := by
  funext q
  simp only [inPlace, copiedAtResume, Store.set, h, Int.add_zero]
  by_cases hq : q = p
  · subst hq; simp
  · simp [hq]

end Stilt.Interactions.Resumed
