import Stilt.Quiet.Theorem

/-!
# `io` in rows

`print("hi")` is a read or write of the world, so it types only where the row holds `io`
(E0502, effects.missing-effects): in a body whose row is empty it has no type, and with `io`
it has type `()`. `Shared.new(1)` makes a cell and needs no `io`. A well-typed program whose
`main`'s row holds no `io` writes nothing and reads nothing (`Program.WellTyped.quiet`).
-/

namespace Stilt.Examples.Quiet

private def hi : Expr := .op (.world (.write false true)) [.op (.str "hi") []]

/-- `print("hi")` in a body whose row is empty is E0502. -/
example (D : Decls) (scope : RowScope) (Γ : Ctx) (τ : Ty) :
    ¬ HasType D scope Γ (Effects.body Row.pure .unit) hi τ := by
  intro h
  cases h with
  | op _ _ _ _ hio => exact absurd (hio rfl) (by simp [Effects.body])

/-- With `io` in the row, `print("hi")` has type `()`. -/
example (D : Decls) (scope : RowScope) (Γ : Ctx) :
    HasType D scope Γ (Effects.body { Row.pure with io := true } .unit) hi .unit :=
  .op (.world .write) (.cons (.op .str .nil (Op.keysIn_of_nil rfl) (Op.boundsIn_of_nil rfl)
      (Op.noIo rfl)) (.refl _) .nil)
    (Op.keysIn_of_nil rfl) (Op.boundsIn_of_nil rfl) fun _ => rfl

/-- `Shared.new(1)` needs no `io`. -/
example : (Op.world (.sharedNew .i64)).io = false := rfl

/-- A program whose `main`'s row holds no `io` ends with nothing written and its input
unread, on every input and at every fuel. -/
example (p : Program) (hp : p.WellTyped) (hio : p.row.io = false) (input : String) :
    ∀ w ∈ (p.runCopy 100 input).world, w.out = "" ∧ w.input = input := fun w hw =>
  let ⟨h₁, _, h₃⟩ := hp.quiet hio 100 input w hw
  ⟨h₁, h₃⟩

end Stilt.Examples.Quiet
