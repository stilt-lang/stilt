import Stilt.Sharing.Alias

/-!
# `let` and `var` with sharing

A `let` or a `var` runs alike with copies and with sharing when every binding is shared: its
initializer runs alike, and its body runs with the name bound, in a new home or, for an
initializer that names a place at a copy-on-write type, referring to the place, which holds the
initializer's value (modes.copies).
-/

namespace Stilt.Sharing

open InPlace (Ref)

/-- The body, run with the name bound to the initializer's value. -/
theorem Corr.bound (D : Decls) {shared : Name → Bool} (hsh : ∀ y, shared y = true) (x : Name)
    (τ : Ty) (init : Expr) {v : Value} (hv : v.Safe) {m : Eval Copy.State Value}
    {m' : Eval (State × World) Value} (hm : Sim Value.Safe m m') {fr : Copy.State}
    {s : State × World} (hs : AgreesIn fr s)
    (ha : ∀ r, aliasRef? s.1 init = some r → deref s.1 r [] = .ok v ∧ r.toPath.Under s.1.paths) :
    Corr Value.Safe s.1 (Eval.withInit Copy.memory x init v m fr) (bindIn D shared x τ init v m' s) := by
  have hc : Eval.withInit Copy.memory x init v m = Eval.withVar Copy.memory x v m := by
    cases init <;> rfl
  rw [hc]
  have hu : (!shared x) = false := by simp [hsh x]
  unfold bindIn
  simp only [hu]
  have hw : Corr Value.Safe s.1 (Eval.withVar Copy.memory x v m fr)
      ((m' (bindWith s.1 x v false (D.cow τ), s.2)).unbind (memory shared)) :=
    Corr.scoped shared hm ⟨hs.1.bindWith x hv false _, hs.2.1.cons rfl rfl rfl rfl, hs.2.2⟩
      (Grown.bindWith s.1 x v false _) rfl
  cases hr : aliasRef? s.1 init with
  | none => exact hw
  | some r =>
    dsimp only
    split
    · obtain ⟨hd, hun⟩ := ha r hr
      exact Corr.scoped shared hm ⟨hs.1.bindAlias x hv hd false, hs.2.1.cons rfl rfl rfl rfl, hs.2.2⟩
        (Grown.bindAlias s.1 x v hun false) rfl
    · exact hw

/-- A `let` or a `var`: its initializer, then its body with the name bound, sharing the place
the initializer names when it names one (modes.copies). -/
theorem Sim.letIn (D : Decls) {shared : Name → Bool} (hsh : ∀ y, shared y = true) (x : Name)
    (τ : Ty) (init : Expr) {mi : Eval Copy.State Value} {mi' : Eval (State × World) Value}
    (hi : Sim Value.Safe mi mi')
    (ha : ∀ s v s₁, mi' s = .done v s₁ → ∀ r, aliasRef? s₁.1 init = some r →
      deref s₁.1 r [] = .ok v ∧ r.toPath.Under s₁.1.paths)
    (hsimple : init.pureIndexes = true → ∀ s, (mi' s).Simple)
    {m : Eval Copy.State Value} {m' : Eval (State × World) Value} (hm : Sim Value.Safe m m') :
    Sim Value.Safe (mi >>= fun v => Eval.withInit Copy.memory x init v m)
      (mi' >>= fun v => bindIn D shared x τ init v m') := by
  by_cases hp : init.pureIndexes = true
  · intro fr s hs
    show Corr Value.Safe s.1 ((mi fr).bind fun v fr' => Eval.withInit Copy.memory x init v m fr')
      ((mi' s).bind fun v s' => bindIn D shared x τ init v m' s')
    have hsm := hsimple hp s
    rcases (hi fr s hs).cases with ⟨v, fr₁, s₁, h₁, h₂, hv, hag, hev⟩ |
      ⟨e, fr₁, s₁, h₁, h₂, -⟩ | ⟨j, fr₁, s₁, h₁, h₂, -⟩ | ⟨k, fr₁, s₁, h₁, h₂, hag, hev⟩ |
      ⟨op, v, fr₁, s₁, k, k', h₁, h₂, -⟩ | ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩ <;> rw [h₂] at hsm ⊢ <;> rw [h₁]
    · exact (Corr.bound D hsh x τ init hv hm hag (ha s v s₁ h₂)).follow hev
    · exact hsm.elim
    · exact hsm.elim
    · exact ⟨rfl, hag, hev⟩
    · exact hsm.elim
    · trivial
    · trivial
  · refine Sim.bind hi fun v hv fr s hs => Corr.bound D hsh x τ init hv hm hs fun r hr => ?_
    exact absurd (pureIndexes_of_aliasRef hr) hp

end Stilt.Sharing
