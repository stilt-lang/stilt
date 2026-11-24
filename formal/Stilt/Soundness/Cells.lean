import Stilt.Soundness.Outcome
import Stilt.Cells

/-!
# Typed cells

What keeps a world typed while `when`s hold and put back its cells: holding a cell, putting
back a value of its type, and letting cells go change no cell's type and leave each cell a
value of its type (shared.when). A handle's type tells the values of its cell: those of the
`T` of its `Shared<T>`.
-/

namespace Stilt

variable {D : Decls}

/-- Changing the cell a handle names, keeping its type and leaving a value of its type,
keeps a world typed. -/
theorem World.Typed.modify {w : World} (hw : World.Typed D w) {h : Ty × Nat} {f : Cell → Cell}
    (hf : ∀ c ∈ w.cells, c.type = h.1 → (f c).type = c.type ∧ Value.Typed D (f c).value c.type.sem) :
    World.Typed D (w.modify h f) := by
  intro c' hc'
  rcases Cell.mem_modifyOf hc' with hc' | ⟨c, hc, hu, rfl⟩
  · exact hw c' hc'
  · obtain ⟨ht, hv⟩ := hf c hc hu
    rw [ht]
    exact hv

/-- Holding a cell keeps a world typed. -/
theorem World.Typed.hold {w : World} (hw : World.Typed D w) (h : Ty × Nat) :
    World.Typed D (w.modify h fun c => { c with held := true }) :=
  hw.modify fun c hc _ => ⟨rfl, hw c hc⟩

/-- Putting back a value of the cell's type keeps a world typed. -/
theorem World.Typed.put {w : World} (hw : World.Typed D w) {h : Ty × Nat} {v : Value}
    (hv : Value.Typed D v h.1.sem) (held : Bool) : World.Typed D (w.put h v held) :=
  hw.modify fun _ _ hu => ⟨rfl, hu ▸ hv⟩

/-- Letting cells go keeps a world typed. -/
theorem World.Typed.letGo {w : World} (hw : World.Typed D w) (before : World) :
    World.Typed D (before.letGo w) := by
  intro c' hc'
  obtain ⟨c, hc, h₁, h₂⟩ := Cell.mem_letGo hc'
  rw [h₁, h₂]
  exact hw c hc

/-- Only a `Shared<T>` fits a `Shared<T>`, whose values are the first one's. -/
theorem STy.Fits.shared_values {a c : STy} (h : (STy.shared a).Fits c) :
    ∃ b, c = .shared b ∧ ∀ v, Value.Typed D v a ↔ Value.Typed D v b := by
  generalize ha : STy.shared a = a' at h
  induction h generalizing a with
  | refl => subst ha; exact ⟨a, rfl, fun _ => Iff.rfl⟩
  | eqv hab _ ih =>
    subst ha
    obtain ⟨b₁, rfl, h₁⟩ := hab.shared_inv
    obtain ⟨b, rfl, hb⟩ := ih rfl
    exact ⟨b, rfl, fun v => ⟨fun hv => (hb v).1 (hv.eqv h₁), fun hv => ((hb v).2 hv).eqv h₁.symm⟩⟩
  | grow _ _ _ => cases ha
  | never => cases ha

/-- A value of a `Shared<T>` is a handle, whose cell's values are those of `T`. -/
theorem Value.Typed.shared_inv {v : Value} {a : STy} (hv : Value.Typed D v (.shared a)) :
    ∃ u k, v = .handle u k ∧ ∀ x, Value.Typed D x u.sem ↔ Value.Typed D x a := by
  cases hv with
  | handle h =>
    obtain ⟨b, hb, hx⟩ := STy.Fits.shared_values (D := D) h
    cases hb
    exact ⟨_, _, rfl, hx⟩
  | closure _ _ _ _ _ _ _ h _ => obtain ⟨_, _, _, h⟩ := h.fn_fn rfl; exact nomatch h
  | function _ _ _ h => obtain ⟨_, _, _, h⟩ := h.fn_fn rfl; exact nomatch h

end Stilt
