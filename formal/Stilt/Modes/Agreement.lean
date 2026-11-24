import Stilt.Modes.Facts
import Stilt.Modes.Gate
import Stilt.Moves.Theorem

/-!
# Modes change nothing a run observes

modes.fact-not-type: evaluation with every mode at its default agrees with
evaluation that reuses a `once` closure's captures and the memory of `local`,
`unique` values.

The evaluation that reuses memory is `Moving` (`Stilt.Moves.Memory`), in
which a mark `move x` hands the storage of `x` over to the binding or the
parameter that takes its value. `Program.markModes` keeps, of the marks that
`Program.markMoves` puts at every last use, those that the modes allow
(`ModeCtx.reuse`), and reads the others as variables, which copy:

* the last use of a `local`, `unique` binding: a `let` or `var` binding or a
  `let` parameter whose value doesn't leave the function, and which no write
  shares (modes.escaping and modes.shared-writes);
* in the body of a `once` closure literal, the last use of a capture, which
  the closure gives up at its one call (modes.once-parameters), as a consumed parameter gives
  up its argument.

Evaluation with every mode at its default is copy-in, copy-out, the reference interpreter's,
which reads no mode and copies every value it binds or passes. `modesAgreement`
proves that the two give the same observation, up to the marks in the bodies
of the closures that a raised error holds, as `MovingAgreement` does, and
`Program.runCopy_eq_markModes_runMoving_of_raiseFree` exactly when `main`
can't raise.

The proof is `Program.runCopy_eq_markGated_runMoving`: reuse at the marks
that any context keeps agrees with copying, since they are a subset of last
uses (`Expr.movesOk_gate`), and `MovingAgreement` holds for every marking
whose marks are last uses. So it holds whatever the modes say, and that is a
property of the model's memories rather than of the modes: they copy a value
wherever it is bound, captured or passed without a mark, and count no
references, so a last use is all that reuse needs, and `local`, `unique` and
`once` only choose which last uses reuse. A call binds a closure's captures in
storage of the callee's own, so a body could reuse them whatever the closure's
mode; the strategy reuses them only in a `once` closure's body, as `stilt-rc`
does.
-/

namespace Stilt

section Gated

variable {κ : Type} (child : κ → Expr → Nat → κ) (keep : κ → Name → Bool)
  (start : List Param → Expr → κ)

/-- A function with the last uses of its body marked where a context allows
reuse: `start` gives the context of a body from its parameters and itself. -/
def FnDecl.markGated (d : FnDecl) : FnDecl :=
  let marked := d.body.markMoves (inoutLive d.params) false
  { d with body := marked.gate child keep (start d.params d.body) }

theorem FnDecl.markGated_qualify (T : Name) (d : FnDecl) :
    (d.qualify T).markGated child keep start = (d.markGated child keep start).qualify T := rfl

/-- The program with the last uses of each body marked where a context
allows reuse. -/
def Program.markGated (p : Program) : Program :=
  { p with
    decls := p.decls.mapFns (FnDecl.markGated child keep start)
    main := (p.main.markMoves .empty false).gate child keep (start [] p.main) }

theorem Program.markGated_fns (p : Program) :
    (p.markGated child keep start).decls.fns =
      p.decls.fns.map (FnDecl.markGated child keep start) :=
  Decls.fns_mapFns (FnDecl.markGated_qualify child keep start) _

/-- Marking where a context allows erases to the program. -/
theorem Program.erase_markGated (p : Program) : (p.markGated child keep start).erase = p.erase := by
  simp only [Program.erase, Program.markGated, Decls.mapFns_mapFns, Expr.erase_gate,
    Expr.erase_markMoves]
  congr 2
  funext d
  simp [FnDecl.erase, FnDecl.markGated, Expr.erase_gate, Expr.erase_markMoves]

/-- Every mark that a context keeps is a last use. -/
theorem Program.markGated_justified (p : Program) :
    (p.markGated child keep start).MovesJustified := by
  refine ⟨fun d hd => ?_, Expr.movesOk_gate _ _ _ _ _ (Expr.movesOk_markMoves _ _ _)⟩
  rw [Program.markGated_fns, List.mem_map] at hd
  obtain ⟨d, -, rfl⟩ := hd
  exact Expr.movesOk_gate _ _ _ _ _ (Expr.movesOk_markMoves _ _ _)

/-- Marking where a context allows keeps the law of exclusivity. -/
theorem Program.Exclusive.markGated {p : Program} (h : p.Exclusive) :
    (p.markGated child keep start).Exclusive := by
  refine ⟨fun d hd => ?_, ?_⟩
  · rw [Program.markGated_fns, List.mem_map] at hd
    obtain ⟨d, hd, rfl⟩ := hd
    simpa [FnDecl.markGated, Expr.exclusive_gate, Expr.exclusive_markMoves] using h.1 d hd
  · simpa [Program.markGated, Expr.exclusive_gate, Expr.exclusive_markMoves] using h.2

/-- **Reuse at any subset of last uses can't be observed.** On a well-typed
program that obeys the law of exclusivity, copy-in, copy-out and `Moving` on
the program marked where any context allows give the same observation and write
the same output, with the same fuel and input, once the marks in the error raised
are erased. -/
theorem Program.runCopy_eq_markGated_runMoving (p : Program) (fuel : Nat) (input : String)
    (hwt : p.WellTyped) (hex : p.Exclusive) :
    (p.runCopy fuel input).shows =
      ((p.markGated child keep start).runMoving fuel input).shows.map Observation.eraseRaised id := by
  have hwt' : (p.markGated child keep start).erase.WellTyped := by
    rw [p.erase_markGated, hwt.erase_eq]
    exact hwt
  rw [← movingAgreement _ fuel input hwt' (hex.markGated child keep start) (p.markGated_justified ..),
    Program.runCopy_shows_erase hwt', p.erase_markGated, hwt.erase_eq]

end Gated

/-- The program with the last uses of each body marked where the modes of its
bindings allow reuse: of a `local`, `unique` binding, or of a capture of a
`once` closure in its body (modes.fact-not-type). -/
def Program.markModes (p : Program) : Program :=
  p.markGated p.modeEnv.child ModeCtx.reuse p.modeEnv.start

/-- **Modes agreement** (modes.fact-not-type). On a well-typed program that
obeys the law of exclusivity, copy-in, copy-out, which reads no mode, and
`Moving` on the program marked where its modes allow reuse give the same
observation and write the same output, with the same fuel and input, once the
marks in the error raised are erased. -/
def ModesAgreement : Prop :=
  ∀ (p : Program) (fuel : Nat) (input : String), p.WellTyped → p.Exclusive →
    (p.runCopy fuel input).shows = (p.markModes.runMoving fuel input).shows.map Observation.eraseRaised id

/-- **Modes agreement**, proved: the reuse that the modes allow can't be
observed. -/
theorem modesAgreement : ModesAgreement := fun p fuel input hwt hex =>
  p.runCopy_eq_markGated_runMoving _ _ _ fuel input hwt hex

/-- **Modes change nothing a `main` that can't raise shows.** A well-typed
program that obeys the law of exclusivity and whose row has no `raise` shows
under copy-in, copy-out exactly what it shows under `Moving` with the reuse its
modes allow, with the same fuel. -/
theorem Program.runCopy_eq_markModes_runMoving_of_raiseFree (p : Program) (fuel : Nat)
    (input : String) (hwt : p.WellTyped) (hex : p.Exclusive) (hrow : p.row.raise = none) :
    (p.runCopy fuel input).shows = (p.markModes.runMoving fuel input).shows := by
  have h := modesAgreement p fuel input hwt hex
  refine Prod.ext ?_ (congrArg Prod.snd h : _ = id _)
  replace h := congrArg Prod.fst h
  simp only [Outcome.shows, Prod.map] at h ⊢
  cases ho : (p.markModes.runMoving fuel input).observe with
  | raised e =>
    rw [ho] at h
    cases hrun : p.runCopy fuel input with
    | raised e' s => exact absurd hrun (raiseFree p fuel input hwt hrow e' s)
    | _ => simp [hrun, Outcome.observe, Observation.eraseRaised] at h
  | _ => rw [ho] at h; exact h

end Stilt
