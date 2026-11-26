import Stilt.Sharing.Steps
import Stilt.Free

/-!
# Capturing with sharing

A closure literal captures the same values with copies and with sharing: copy-in, copy-out
keeps the newest binding of each variable of its frame that the closure captures, and sharing
reads those bindings where they refer, which a frame that agrees on every binding holds alike
(expressions.capture).
-/

namespace Stilt.Sharing

theorem readCaptured_holds {st : Array Value} {env₀ : List (Name × Entry)} :
    ∀ (keep : Name → Bool) {fr : Copy.Frame} {env : List (Name × Entry)}, Holds st fr env →
      readCaptured ⟨env₀, st⟩ (newestOf keep env) = .ok (newestOf keep fr)
  | _, [], [], _ => rfl
  | keep, (x, v) :: fr, (_, e) :: env, ⟨rfl, hd, h⟩ => by
    have hd' : deref ⟨env₀, st⟩ e.ref [] = .ok v := hd
    by_cases hk : keep x = true
    · have ih := readCaptured_holds (env₀ := env₀) (fun y => keep y && y != x) h
      unfold readCaptured at ih ⊢
      simp only [newestOf, hk, ↓reduceIte, List.mapM_cons, hd', ih]
      rfl
    · have ih := readCaptured_holds (env₀ := env₀) keep h
      simp only [newestOf, hk, Bool.false_eq_true, ↓reduceIte, ih]
  | _, [], _ :: _, h => h.elim
  | _, _ :: _, [], h => h.elim

/-- A closure literal captures the same safe values in both models (expressions.capture). -/
theorem Sim.captured (ps : List Param) (body : Expr) :
    Sim (fun captured : List (Name × Value) => ∀ xv ∈ captured, xv.2.Safe)
      (Eval.inspect (Copy.memory.capture · (Expr.captures ps body)))
      (Eval.inspect fun s => readCaptured s.1 (captureOf ps body s.1.env)) := by
  refine Sim.inspect fun fr s hs => ⟨?_, fun _ ha => ?_⟩
  · have hh : Holds s.1.store fr.1 s.1.env := by
      have := hs.1.holds
      rwa [Moving.keep_all (by simp) (by simp), Moving.keep_all (by simp)
        (by simp [hs.1.len_env.symm])] at this
    exact (readCaptured_holds (Expr.captures ps body) hh).symm
  · cases ha
    exact captureOf_forall hs.1.safe

/-- A closure literal is the same safe value in both models (expressions.capture). -/
theorem Sim.closure (ps : List Param) (result : Ty) (ρ : Row)
    (body : Expr) (hsafe : ∀ c, (∀ xv ∈ c, xv.2.Safe) → (Value.closure c ps result ρ body).Safe) :
    Sim Value.Safe
      (Eval.inspect (Copy.memory.capture · (Expr.captures ps body)) >>= fun c =>
        Pure.pure (Value.closure c ps result ρ body))
      (Eval.inspect (fun s : State × World => readCaptured s.1 (captureOf ps body s.1.env)) >>=
        fun c => Pure.pure (Value.closure c ps result ρ body)) :=
  Sim.bind (Sim.captured ps body) fun c hc => Sim.pure (hsafe c hc)

end Stilt.Sharing
