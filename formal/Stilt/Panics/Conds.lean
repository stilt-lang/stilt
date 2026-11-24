import Stilt.Panics.Calls
import Stilt.Panics.Facts

/-!
# Conditions and divisors

A condition gives the branches it guards its facts (facts.guarding-tests): a
test of a variable against zero reads it and changes nothing, so the branch it
takes starts from the same frame, in which the variable holds the integer it
compared. A divisor that a test guards, read after the operand before it,
which doesn't write it, holds an integer other than zero.
-/

namespace Stilt

namespace Eval.PanicFree

variable {D : Decls} (w : WriteBack) {G : List Known} {α : Type} {P : α → Prop}

/-- The two operands of an operation, the second guarded by what the first doesn't write. -/
theorem pair {run : Expr → Eval Copy.State Value} {a b : Expr} {W₁ W₂ L₁ L₂ : List Name}
    {P₁ P₂ : Value → Prop} (ha : Eval.PanicFree G P₁ (run a))
    (ka : Eval.Keeps W₁ L₁ (fun _ => True) (run a))
    (hb : Eval.PanicFree (withoutNames G W₁) P₂ (run b)) (kb : Eval.Keeps W₂ L₂ (fun _ => True) (run b)) :
    Eval.PanicFree G (fun vs => ∃ u v, vs = [u, v] ∧ P₁ u ∧ P₂ v) (Eval.list run [a, b]) := by
  unfold Eval.list Eval.list Eval.list
  have inner : Eval.PanicFree (withoutNames G W₁) (fun vs => ∃ v, vs = [v] ∧ P₂ v)
      (do let v ← run b; let vs ← (Pure.pure [] : Eval Copy.State (List Value)); Pure.pure (v :: vs)) :=
    bind hb kb fun v hv => bind (W := []) (L := []) (R := fun _ => True)
      (pure (P := fun vs : List Value => vs = []) rfl)
      (Eval.Keeps.pure trivial) fun vs hvs => pure ⟨v, by rw [hvs], hv⟩
  have kinner : Eval.Keeps W₂ L₂ (fun _ => True)
      (do let v ← run b; let vs ← (Pure.pure [] : Eval Copy.State (List Value)); Pure.pure (v :: vs)) :=
    Eval.Keeps.bind kb fun _ _ =>
      Eval.Keeps.bind (P := fun _ : List Value => True) (Eval.Keeps.pure trivial) fun _ _ =>
        Eval.Keeps.pure trivial
  exact bind ha ka fun u hu => bind inner kinner fun vs ⟨v, hvs, hv⟩ => pure ⟨u, v, by rw [hvs], hu, hv⟩

theorem intLit (n : Nat) (k : Int) :
    Eval.PanicFree G (fun v => v = .int k) (eval D (Copy.memoryWith w) n (.int k)) := by
  cases n
  · exact outOfFuel
  · exact pure rfl

/-- A variable that a test guards holds an integer other than zero. -/
theorem readNonzero (n : Nat) {d : Name} (hd : Known.nonzero d ∈ G) :
    Eval.PanicFree G (fun v => ∃ k, v = .int k ∧ k ≠ 0) (eval D (Copy.memoryWith w) n (.var d)) := by
  cases n
  · exact outOfFuel
  · intro s hs hz
    obtain ⟨k, hk, hk0⟩ := hz _ hd
    show Outcome.PanicFree _ (Eval.inspect (fun s : Copy.State => Copy.read s.1 d []) s)
    simp only [Eval.inspect, Eval.ofExcept, Copy.read, hk, Value.get]
    exact ⟨⟨k, rfl, hk0⟩, hs⟩

/-- An `if` or a `while`: the branch a condition takes may count on the facts it gives
(`eval_facts`). -/
theorem cond (n : Nat) (ih : PanicFreeRun (eval D (Copy.memoryWith w) n)) {c : Expr}
    (hc : c.panicFreeIn G = true) {ma mb : Eval Copy.State α}
    (ha : Eval.PanicFree (withoutNames G c.writes ++ c.facts) P ma)
    (hb : Eval.PanicFree (withoutNames G c.writes ++ c.negFacts) P mb) :
    Eval.PanicFree G P ((eval D (Copy.memoryWith w) n c >>= Eval.asBool) >>= fun v =>
      if v then ma else mb) :=
  have kc := eval_keeps D w n c c.writes c.resizes (List.Subset.refl _) (List.Subset.refl _)
  bindAfter (F := fun v => c.factsAs v)
    (bind (ih G c hc) kc fun _ _ => asBool)
    (Eval.Keeps.bind kc fun v _ => Eval.Keeps.asBool v)
    (fun s v s' h => by
      obtain ⟨u, s₁, h₁, h₂⟩ := Eval.bind_reaches h
      obtain ⟨hu, hs⟩ := Eval.asBool_reaches h₂
      subst hu
      rw [hs]
      exact eval_facts w n c v s s₁ h₁)
    fun v _ => by
      cases v
      · exact hb
      · exact ha

end Eval.PanicFree

end Stilt
