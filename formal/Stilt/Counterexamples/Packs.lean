import Stilt.Poly.Packs

/-!
# Indexing a pack tuple

`spread_map` holds at every pack, the empty one included, because a spread
only maps over a pack tuple. Reading its first element, `xs.0`, has the type
of the pack's first element, which some instantiations have and others
don't: at `Ts = (i64,)` it is `i64`, and at the empty pack, which a call such
as `f(())` gives (variadics.empty-pack), the tuple has no element 0, so `xs.0` has
no type at all. A body that read it would be well typed at some
instantiations only, which is why variadics.pack-tuples rejects it (E0342), as
`first` in the conformance suite's `variadics/errors.lt`.
-/

namespace Stilt.Packs

/-- The type of `xs.0`, for `xs: (..t)` at the pack `ts`: the type of the
tuple's first element, if it has one. -/
def firstTy (t : Ty) (ts : List Ty) : Option Ty := (spreadTy t ts).head?

/-- At `Ts = (i64,)`, `xs.0` has type `i64`. -/
theorem first_at_one : firstTy .elem [.int] = some .int := rfl

/-- At the empty pack, `xs.0` has no type: the tuple has no element 0. -/
theorem first_at_none : firstTy .elem [] = none := rfl

/-- So no type is the type of `xs.0` at every pack: E0342. -/
theorem first_ill_typed : ¬ ∃ u, ∀ ts, firstTy .elem ts = some u := by
  intro ⟨u, h⟩
  have := h []
  rw [first_at_none] at this
  cases this

/-- Its value doesn't exist either: the pack tuple of the empty pack is `()`,
whose first element is nothing. -/
theorem first_value_at_none (vs : List Val)
    (h : Pairwise (fun v a => ValTy v (Ty.elem.at a)) vs []) : vs.head? = none := by
  cases h
  rfl

end Stilt.Packs
