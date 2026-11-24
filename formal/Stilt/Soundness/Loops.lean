import Stilt.Soundness.Forms

/-!
# Loops and jumps

A `while` and a `loop` run turns of their body, each followed by the loop
again, which rests on the lemma at the fuel below for the loop itself. A turn
ends the loop only when the body breaks out, which its effects allow inside a
loop's body (expressions.break-and-continue), so a `loop` whose body may not
break out never ends with a value, as its type `Never` says
(expressions.loop-types). `break`, `continue` and `return` are jumps that
their effects allow, a `return`'s value of its body's result type
(expressions.closure-boundaries).
-/

namespace Stilt

section

variable {D : Decls} {n : Nat} (hs : Sound D n) {scope : RowScope} {η : REnv}
  (hη : η.Respects scope) (θ : RowSubst) {Γ : Ctx} {fx : Effects}
include hs hη

theorem while_ok {c body : Expr} {σc σ : Ty} (hc : HasType D scope Γ fx c σc)
    (hfc : Fits σc .bool) (hb : HasType D scope Γ fx.inLoop body σ) (hfb : Fits σ .unit) :
    Eval.Ok D Γ η (fx.exits D η) (fun v => Value.Typed D v (Ty.unit.close η))
      (eval D Copy.memory (n + 1) ((Expr.while c body).substRows θ)) := by
  have hl := hs (.while hc hfc hb hfb) hη θ
  refine Eval.Ok.bind (P := fun _ => True) (Eval.Ok.bind (hs hc hη θ) fun v hv => ?_) fun k _ => ?_
  · obtain ⟨k, rfl⟩ := (hv.fits (hfc.close η)).bool_inv
    exact Eval.Ok.pure trivial
  · cases k
    · exact Eval.Ok.pure .unit
    · refine Eval.Ok.bind ((hs hb hη θ).turn (X' := fx.exits D η)
        (fun _ F hF he => ⟨F, hF, he⟩) fun _ h => h) fun g _ => ?_
      cases g
      · exact Eval.Ok.pure .unit
      · exact hl

theorem loopBreaks_ok {body : Expr} {σ : Ty} (hb : HasType D scope Γ fx.inLoop body σ)
    (hfb : Fits σ .unit) :
    Eval.Ok D Γ η (fx.exits D η) (fun v => Value.Typed D v (Ty.unit.close η))
      (eval D Copy.memory (n + 1) ((Expr.loop body).substRows θ)) := by
  have hl := hs (.loopBreaks hb hfb) hη θ
  refine Eval.Ok.bind ((hs hb hη θ).turn (X' := fx.exits D η)
    (fun _ F hF he => ⟨F, hF, he⟩) fun _ h => h) fun g _ => ?_
  cases g
  · exact Eval.Ok.pure .unit
  · exact hl

/-- A `loop` whose body may not break out ends only by raising, returning or
panicking, or by running out of fuel (expressions.loop-types). -/
theorem loopForever_ok {body : Expr} {σ : Ty}
    (hb : HasType D scope Γ { fx with continues := true, breaks := false } body σ)
    (hfb : Fits σ .unit) :
    Eval.Ok D Γ η (fx.exits D η) (fun v => Value.Typed D v (Ty.never.close η))
      (eval D Copy.memory (n + 1) ((Expr.loop body).substRows θ)) := by
  have hl := hs (.loopForever hb hfb) hη θ
  refine Eval.Ok.bind ((hs hb hη θ).turn (X' := fx.exits D η)
    (fun _ F hF he => ⟨F, hF, he⟩) fun _ h => h) fun g hg => ?_
  cases g
  · exact (Bool.false_ne_true (hg rfl)).elim
  · exact hl

omit hs hη in
theorem break_ok (h : fx.breaks = true) {τ : Ty} :
    Eval.Ok D Γ η (fx.exits D η) (fun v => Value.Typed D v (τ.close η))
      (eval D Copy.memory (n + 1) (Expr.break.substRows θ)) :=
  Eval.Ok.jump h

omit hs hη in
theorem continue_ok (h : fx.continues = true) {τ : Ty} :
    Eval.Ok D Γ η (fx.exits D η) (fun v => Value.Typed D v (τ.close η))
      (eval D Copy.memory (n + 1) (Expr.continue.substRows θ)) :=
  Eval.Ok.jump h

theorem return_ok {e : Expr} {σ τ : Ty} (he : HasType D scope Γ fx e σ) (hfit : Fits σ fx.result) :
    Eval.Ok D Γ η (fx.exits D η) (fun v => Value.Typed D v (τ.close η))
      (eval D Copy.memory (n + 1) ((Expr.return e).substRows θ)) :=
  Eval.Ok.bind (hs he hη θ) fun _ hv => Eval.Ok.jump (hv.fits (hfit.close η))

end

end Stilt
