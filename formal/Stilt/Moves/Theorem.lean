import Stilt.Moves.Simulation
import Stilt.Moves.Unmarked
import Stilt.Moves.Oracle
import Stilt.Soundness.Theorem

/-!
# Moving at a last use

The proof of `MovingAgreement`: on a program whose erasure is well typed,
that obeys the law of exclusivity, and whose marks are last uses, copy-in,
copy-out and `Moving` give the same observation (values.passing-values).

`Program.markMoves` marks every argument and initializer that is a variable at
its last use, as the compiler infers it. Its marks are last uses
(`Program.markMoves_justified`), it erases to the program, and it keeps the
law of exclusivity, so the theorem applies to every well-typed program that
obeys the law, once marked. Copy-in, copy-out runs the marked program as the
program, up to the marks in the error it raises (`Program.runCopy_eraseRaised`):
the value it returns is `()` (program.main), but the error may hold a
closure, whose body carries the marks. The records show that error through its
`Show` (program.main and program.exit-statuses), a trait of the prelude, which the model
leaves out. So `Moving` runs the marked program as copy-in, copy-out runs the
program, up to those marks (`Program.runCopy_eq_markMoves_runMoving`), and
with nothing erased if the row of `main` has no `raise`
(`Program.runCopy_eq_markMoves_runMoving_of_raiseFree`).
-/

namespace Stilt

/-- **Moving agreement**. On a program whose erasure is well typed, that obeys
the law of exclusivity, and whose marks are last uses, copy-in, copy-out (the
reference interpreter's model, values.inout-arguments) and `Moving`, in which a last use hands its
storage over to the binding or the parameter that receives it, give the same
observation and write the same output, with the same fuel and input. This is the
claim of values.passing-values: the reuse that a last use allows can't be observed. -/
def MovingAgreement : Prop :=
  ∀ (p : Program) (fuel : Nat) (input : String), p.erase.WellTyped → p.Exclusive →
    p.MovesJustified → (p.runCopy fuel input).shows = (p.runMoving fuel input).shows

open Moving in
/-- A program whose erasure is well typed, that obeys the law, and whose marks
are last uses has declarations that `Moving` runs alike. -/
theorem Program.declsOk {p : Program} (hwt : p.erase.WellTyped) (hex : p.Exclusive)
    (hmv : p.MovesJustified) : DeclsOk p.decls := fun d hd => by
  have hd' : d.erase ∈ p.erase.decls.fns := p.erase_fns ▸ List.mem_map_of_mem hd
  obtain ⟨σ, hty, -⟩ := hwt.typedIn.fns d.erase hd'
  refine ⟨hwt.decls.paramNames d.erase hd', hex.1 d hd, ?_, hmv.1 d hd⟩
  rw [← Expr.distinctParams_erase]
  exact hty.distinctParams

open Moving InPlace in
/-- **Moving agreement**, proved. -/
theorem movingAgreement : MovingAgreement := by
  intro p fuel input hwt hex hmv
  have hmain : p.main.Safe := by
    obtain ⟨σ, hty, -⟩ := hwt.main
    refine ⟨⟨[], hex.2⟩, ?_⟩
    rw [← Expr.distinctParams_erase]
    exact hty.distinctParams
  have hag : MAgrees [] [] ⟨[], []⟩ :=
    ⟨rfl, rfl, ⟨trivial, .nil, by simp [keep]⟩, by simp [Valid], by simp [keep]⟩
  have hc := eval_msim (p.declsOk hwt hex hmv) fuel p.main .empty hmain hmv.2
    ([], World.start input) (⟨[], []⟩, World.start input) [] ⟨hag, rfl, World.All.start input⟩
    ⟨fun _ _ => trivial, fun _ b hb => by simp at hb⟩
  unfold Program.runCopy Program.runMoving Program.run
  rcases hc.cases with ⟨v, ⟨_, x⟩, ⟨_, y⟩, h₁, h₂, -, ⟨_, ⟨-, hw, -⟩, -⟩⟩ |
    (⟨e, ⟨_, x⟩, ⟨_, y⟩, h₁, h₂, -, ⟨_, ⟨-, hw, -⟩, -⟩⟩ | ⟨j, ⟨_, x⟩, ⟨_, y⟩, h₁, h₂, -, ⟨_, ⟨-, hw, -⟩, -⟩⟩) |
    ⟨k, ⟨_, x⟩, ⟨_, y⟩, h₁, h₂, ⟨_, ⟨-, hw, -⟩, -⟩⟩ | ⟨_, _, _, _, _, _, h₁, h₂, -⟩ | ⟨h₁, h₂⟩ |
    ⟨h₁, h₂⟩ <;> rw [h₁, h₂] <;> (try cases (show x = y from hw)) <;> first | rfl | (cases j <;> rfl)

/-- In particular the two models observe the same. -/
theorem movingAgreement_observe (p : Program) (fuel : Nat) (input : String) (hwt : p.erase.WellTyped)
    (hex : p.Exclusive) (hmv : p.MovesJustified) :
    (p.runCopy fuel input).observe = (p.runMoving fuel input).observe :=
  congrArg Prod.fst (movingAgreement p fuel input hwt hex hmv)

/-- And they write the same output. -/
theorem movingAgreement_output (p : Program) (fuel : Nat) (input : String) (hwt : p.erase.WellTyped)
    (hex : p.Exclusive) (hmv : p.MovesJustified) :
    (p.runCopy fuel input).output = (p.runMoving fuel input).output :=
  congrArg Prod.snd (movingAgreement p fuel input hwt hex hmv)

/-- Marking last uses keeps the law of exclusivity: the law looks at places,
which marks don't change. -/
theorem Expr.exclusive_markMoves (e : Expr) (L : Live) (b : Bool) (r : List Shape) :
    (e.markMoves L b).exclusive r = e.exclusive r := by
  rw [← Expr.exclusive_erase, Expr.erase_markMoves, Expr.exclusive_erase]

theorem Program.Exclusive.markMoves {p : Program} (h : p.Exclusive) : p.markMoves.Exclusive := by
  refine ⟨fun d hd => ?_, by simpa [Program.markMoves, Expr.exclusive_markMoves] using h.2⟩
  rw [Program.markMoves_fns, List.mem_map] at hd
  obtain ⟨d, hd, rfl⟩ := hd
  simpa [FnDecl.markMoves, Expr.exclusive_markMoves] using h.1 d hd

/-- A well-typed program, marked, erases to itself, which is well typed. -/
theorem Program.WellTyped.markMoves {p : Program} (h : p.WellTyped) : p.markMoves.erase.WellTyped := by
  rw [Program.erase_markMoves, h.erase_eq]
  exact h

/-- **Inferred moves can't be observed.** A well-typed program that obeys the
law of exclusivity, with every argument and initializer that is a variable at
its last use marked, runs alike under copy-in, copy-out and `Moving`. -/
theorem markMoves_agreement (p : Program) (fuel : Nat) (input : String) (hwt : p.WellTyped)
    (hex : p.Exclusive) :
    (p.markMoves.runCopy fuel input).shows = (p.markMoves.runMoving fuel input).shows :=
  movingAgreement p.markMoves fuel input hwt.markMoves hex.markMoves p.markMoves_justified

/-- **Copy-in, copy-out runs a typed program as its erasure.** On a program
whose erasure is well typed, what a run shows, with the marks of the error it
raises erased, is what a run of its erasure shows, with the same fuel. A value
that it returns is `()`, which has no marks (values.passing-values; program.main). -/
theorem Program.runCopy_eraseRaised {p : Program} (hwt : p.erase.WellTyped) (fuel : Nat)
    (input : String) :
    (p.runCopy fuel input).observe.eraseRaised = (p.erase.runCopy fuel input).observe := by
  rw [← p.runCopy_erase fuel input]
  cases ho : (p.runCopy fuel input).observe with
  | returned v =>
    have h := p.runCopy_erase fuel input
    rw [ho] at h
    obtain rfl := Value.erase_eq_unit.1 (hwt.returned_unit fuel input h.symm)
    rfl
  | jumped j =>
    have h := p.runCopy_erase fuel input
    rw [ho] at h
    exact (hwt.not_jumped fuel input _ h.symm).elim
  | _ => rfl

/-- What a run of a program shows, the marks of its raised error erased, is what a run of its
erasure shows, and both write the same output. -/
theorem Program.runCopy_shows_erase {p : Program} (hwt : p.erase.WellTyped) (fuel : Nat)
    (input : String) :
    (p.runCopy fuel input).shows.map Observation.eraseRaised id = (p.erase.runCopy fuel input).shows :=
  Prod.ext (p.runCopy_eraseRaised hwt fuel input) (p.runCopy_output_erase fuel input)

/-- **Marks change only the bodies that a raise shows.** A well-typed program,
with every argument and initializer that is a variable at its last use marked,
shows under copy-in, copy-out what the program shows, once the marks in the
error it raises are erased (values.passing-values). -/
theorem Program.markMoves_runCopy (p : Program) (fuel : Nat) (input : String) (hwt : p.WellTyped) :
    (p.markMoves.runCopy fuel input).shows.map Observation.eraseRaised id = (p.runCopy fuel input).shows := by
  rw [Program.runCopy_shows_erase hwt.markMoves, Program.erase_markMoves, hwt.erase_eq]

/-- **Moving at inferred last uses agrees with the reference interpreter.** A well-typed
program that obeys the law of exclusivity shows under copy-in, copy-out (the
reference interpreter's model, values.inout-arguments) what its marking shows under `Moving`, in
which each last use hands its storage over, with the same fuel, once the
marks in the error it raises are erased. Erasing touches only the bodies of
closures that the error holds (values.passing-values), since the value returned is
`()` (program.main). The error may hold a closure: the records show it
through its `Show` (program.main and program.exit-statuses), which the model, having no
traits, can't state. -/
theorem Program.runCopy_eq_markMoves_runMoving (p : Program) (fuel : Nat) (input : String)
    (hwt : p.WellTyped) (hex : p.Exclusive) :
    (p.runCopy fuel input).shows = (p.markMoves.runMoving fuel input).shows.map Observation.eraseRaised id := by
  rw [← markMoves_agreement p fuel input hwt hex, p.markMoves_runCopy fuel input hwt]

/-- **Moving agrees with the reference interpreter exactly on a `main` that can't raise.** A
well-typed program that obeys the law of exclusivity and whose row has no
`raise` shows under copy-in, copy-out exactly what its marking shows under
`Moving`, with the same fuel. -/
theorem Program.runCopy_eq_markMoves_runMoving_of_raiseFree (p : Program) (fuel : Nat)
    (input : String) (hwt : p.WellTyped) (hex : p.Exclusive) (hrow : p.row.raise = none) :
    (p.runCopy fuel input).shows = (p.markMoves.runMoving fuel input).shows := by
  have h := p.runCopy_eq_markMoves_runMoving fuel input hwt hex
  refine Prod.ext ?_ (congrArg Prod.snd h : _ = id _)
  replace h := congrArg Prod.fst h
  simp only [Outcome.shows, Prod.map] at h ⊢
  cases ho : (p.markMoves.runMoving fuel input).observe with
  | raised e =>
    rw [ho] at h
    cases hrun : p.runCopy fuel input with
    | raised e' s => exact absurd hrun (raiseFree p fuel input hwt hrow e' s)
    | _ => simp [hrun, Outcome.observe, Observation.eraseRaised] at h
  | _ => rw [ho] at h; exact h

end Stilt
