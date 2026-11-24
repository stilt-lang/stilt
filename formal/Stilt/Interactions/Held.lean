/-!
# `when` and the law of exclusivity

shared.names-that-may-be-one-place: the names of one `when` whose values have the same type are
one binding for the law of exclusivity. The model gives each name of a `when`
the value it reaches and its value's type, one value having one type; a place
is a name and a field, and two places of one call's `inout` arguments overlap
under shared.names-that-may-be-one-place when their names' types are the same and their fields are.
`accepted_disjoint` proves that places shared.names-that-may-be-one-place accepts are different places of
the store even when two names reach one value, `both_agree` that copying such
arguments in and writing them back then leaves the store that writing in place
leaves, and `aliased_differ` that without shared.names-that-may-be-one-place, `both` of shared.names-that-may-be-one-place leaves
different stores: 10 copied and 11 in place.

shared.when-on-value-already-held: the running `when`s are a stack of the values each holds, and a `when`
enters only when none of its values is held, or panics. `enter_keeps` and
`leave_keeps` prove that no value is ever held by two running `when`s.
-/

namespace Stilt.Interactions.Held

/-- A shared value, by its identity. -/
abbrev Value := Nat

/-- The names of a `when`: the value each reaches and its value's type. -/
structure Names where
  cell : Nat → Value
  ty : Nat → Nat
  /-- One value has one type. -/
  typed : ∀ a b, cell a = cell b → ty a = ty b

/-- A place rooted in a name of the `when`: the name and a field of its
value. -/
structure Place where
  name : Nat
  field : Nat

/-- shared.names-that-may-be-one-place: two places overlap when their names' values have the same type and
their fields are the same, whichever values the names reach. -/
def Overlapping (w : Names) (a b : Place) : Prop :=
  w.ty a.name = w.ty b.name ∧ a.field = b.field

/-- The place of the store that a place reaches: its value and its field. -/
def Names.reach (w : Names) (a : Place) : Value × Nat :=
  (w.cell a.name, a.field)

/-- Places that shared.names-that-may-be-one-place accepts reach different places of the store. -/
theorem accepted_disjoint (w : Names) (a b : Place) (h : ¬ Overlapping w a b) :
    w.reach a ≠ w.reach b := by
  intro he
  simp only [Names.reach, Prod.mk.injEq] at he
  exact h ⟨w.typed _ _ he.1, he.2⟩

/-- A store of the fields of shared values. -/
abbrev Store := Value × Nat → Int

/-- `s` with the place `p` holding `v`. -/
def Store.set (s : Store) (p : Value × Nat) (v : Int) : Store :=
  fun q => if q = p then v else s q

/-- `both(inout x, inout y)` of shared.names-that-may-be-one-place, writing in place: 1 added to `x`, then
10 to `y`. -/
def bothInPlace (s : Store) (x y : Value × Nat) : Store :=
  let s1 := s.set x (s x + 1)
  s1.set y (s1 y + 10)

/-- The same call copying its arguments in when it starts and writing them
back from left to right (values.inout-argument-order). -/
def bothCopied (s : Store) (x y : Value × Nat) : Store :=
  (s.set x (s x + 1)).set y (s y + 10)

/-- On different places, the two agree, whatever the order of the
write-back. -/
theorem both_agree (s : Store) (x y : Value × Nat) (h : x ≠ y) :
    bothCopied s x y = bothInPlace s x y := by
  have hy : Store.set s x (s x + 1) y = s y := by
    simp [Store.set, Ne.symm h]
  simp only [bothCopied, bothInPlace, hy]

/-- So for places that shared.names-that-may-be-one-place accepts, the reference interpreter's copies agree with the
compiler's writes in place. -/
theorem accepted_agree (w : Names) (a b : Place) (h : ¬ Overlapping w a b)
    (s : Store) :
    bothCopied s (w.reach a) (w.reach b) = bothInPlace s (w.reach a) (w.reach b) :=
  both_agree s _ _ (accepted_disjoint w a b h)

/-- `pay(acc, acc)` of shared.names-that-may-be-one-place, without shared.names-that-may-be-one-place: `a.balance` and `b.balance` are
one place, and the stores differ. -/
theorem aliased_differ :
    bothCopied (fun _ => 0) (0, 0) (0, 0) (0, 0) ≠
      bothInPlace (fun _ => 0) (0, 0) (0, 0) (0, 0) := by
  simp [bothCopied, bothInPlace, Store.set]

/-- The values that each running `when` holds, the innermost first. -/
abbrev Held := List (List Value)

/-- No value is held by two running `when`s. -/
def Disjoint (held : Held) : Prop :=
  held.Pairwise (fun a b => ∀ v ∈ a, v ∉ b)

/-- shared.when-on-value-already-held: a `when` on `vs` holds them when no running `when` holds any, and
panics, `none`, otherwise. -/
def enter (held : Held) (vs : List Value) : Option Held :=
  if ∃ v ∈ vs, ∃ ws ∈ held, v ∈ ws then none else some (vs :: held)

/-- Entering a `when` keeps every value held by one running `when` at most. -/
theorem enter_keeps (held held' : Held) (vs : List Value) (h : Disjoint held)
    (he : enter held vs = some held') : Disjoint held' := by
  unfold enter at he
  split at he
  · contradiction
  · rename_i hfree
    injection he with he
    subst he
    refine List.Pairwise.cons ?_ h
    intro ws hws v hv hvw
    exact hfree ⟨v, hv, ws, hws, hvw⟩

/-- Leaving the innermost `when` keeps it too. -/
theorem leave_keeps (held : Held) (vs : List Value) (h : Disjoint (vs :: held)) :
    Disjoint held :=
  (List.pairwise_cons.mp h).2

end Stilt.Interactions.Held
