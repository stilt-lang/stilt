import Stilt.Sharing.Assign
import Stilt.Sharing.Let

/-!
# Assignments with sharing

An assignment runs alike with copies and with sharing when every binding is shared: its
indexes and its value run alike, and the write then changes the binding's value alone, either
the whole of it or a part (values.assignment-order, modes.shared-writes).
-/

namespace Stilt.Sharing

open InPlace (Ref)

theorem update_ok {σ α : Type} {f : σ → Except Fault σ} {g : Unit → Eval σ α} {st st' : σ}
    (h : f st = .ok st') : (Eval.update f >>= g) st = g () st' := by
  show (Eval.update f st).bind (fun a s => g a s) = _
  unfold Eval.update
  rw [h]
  rfl

theorem update_error {σ α : Type} {f : σ → Except Fault σ} {g : Unit → Eval σ α} {st : σ}
    {e : Fault} (h : f st = .error e) : (Eval.update f >>= g) st = .fault e st := by
  show (Eval.update f st).bind (fun a s => g a s) = _
  unfold Eval.update
  rw [h]
  cases e <;> rfl

/-- The write that ends an assignment, of a safe value along a path of the place's
projections, from a frame and a state that agree. -/
theorem Corr.assigned {x : Name} {ps : List Projection} {p : Path} (hp : p.Resolves ps)
    {value : Expr} {v : Value} (hv : v.Safe) {fr : Copy.State} {s : State × World}
    (hs : AgreesIn fr s)
    (ha : ∀ r, aliasRef? s.1 value = some r → deref s.1 r [] = .ok v ∧ r.toPath.Under s.1.paths) :
    Corr Value.Safe s.1
      ((Eval.update (fun s => Copy.memory.write s x p v) >>= fun _ => pure .unit) fr)
      ((Eval.update (fun s => (·, s.2) <$>
          if ps.isEmpty then assignWhole s.1 x v (aliasRef? s.1 value) else modify s.1 x p v) >>=
        fun _ => pure .unit) s) := by
  obtain ⟨hag, hsh, hw, hsafe⟩ := hs
  obtain ⟨fr, wd⟩ := fr
  obtain ⟨s, wd'⟩ := s
  simp only at hw
  subst hw
  have hdone : ∀ fr' s', AgreesAll fr' s' → AllShared s' → Follows s s' →
      Corr Value.Safe s (.done Value.unit (fr', wd)) (.done Value.unit (s', wd)) :=
    fun fr' s' hA hS hF => ⟨rfl, .unit, ⟨hA, hS, rfl, hsafe⟩, hF⟩
  have hfail : ∀ f, Corr Value.Safe s (.fault f (fr, wd)) (.fault f (s, wd)) :=
    fun f => Corr.fault ⟨hag, hsh, rfl, hsafe⟩ f
  cases hps : ps.isEmpty
  · rcases hag.modify hsh hv x p with ⟨f, h₁, h₂⟩ | ⟨fr', s', h₁, h₂, hA, hS, hF⟩
    · rw [update_error (e := f) (by simp [Copy.memory, Frames.withWorld, Copy.frames, h₁]; rfl),
        update_error (e := f) (by simp [h₂]; rfl)]
      exact hfail f
    · rw [update_ok (st' := (fr', wd)) (by simp [Copy.memory, Frames.withWorld, Copy.frames, h₁]; rfl),
        update_ok (st' := (s', wd)) (by simp [h₂]; rfl)]
      exact hdone fr' s' hA hS hF
  · have hnil : ps = [] := List.isEmpty_iff.1 hps
    subst hnil
    have hp0 : p = [] := by cases p <;> simp_all [Path.Resolves]
    subst hp0
    rcases hag.assignWhole hsh hv x ha with ⟨f, h₁, h₂⟩ | ⟨fr', s', h₁, h₂, hA, hS, hF⟩
    · rw [update_error (e := f) (by simp [Copy.memory, Frames.withWorld, Copy.frames, h₁]; rfl),
        update_error (e := f) (by simp [h₂]; rfl)]
      exact hfail f
    · rw [update_ok (st' := (fr', wd)) (by simp [Copy.memory, Frames.withWorld, Copy.frames, h₁]; rfl),
        update_ok (st' := (s', wd)) (by simp [h₂]; rfl)]
      exact hdone fr' s' hA hS hF

/-- An assignment: its indexes, then its value, then the write, of the whole of the binding or
of a part (values.assignment-order, modes.shared-writes). -/
theorem Sim.assign {run : Expr → Eval Copy.State Value} {run' : Expr → Eval (State × World) Value}
    (h : SimRun run run') (x : Name) {ps : List Projection} (hps : PathSafe ps) {value : Expr}
    (hval : value.Safe)
    (ha : ∀ s v s₁, run' value s = .done v s₁ → ∀ r, aliasRef? s₁.1 value = some r →
      deref s₁.1 r [] = .ok v ∧ r.toPath.Under s₁.1.paths)
    (hsimple : value.pureIndexes = true → ∀ s, (run' value s).Simple) :
    Sim Value.Safe (Eval.assign Copy.memory run x ps value) (Sharing.assign run' x ps value) := by
  refine Sim.bind (Sim.path h ps hps) fun p hp => ?_
  by_cases hpi : value.pureIndexes = true
  · intro fr s hs
    show Corr Value.Safe s.1 ((run value fr).bind fun v fr' => _)
      ((run' value s).bind fun v s' => _)
    have hsm := hsimple hpi s
    rcases (h value hval fr s hs).cases with ⟨v, fr₁, s₁, h₁, h₂, hv, hag, hev⟩ |
      ⟨e, fr₁, s₁, h₁, h₂, -⟩ | ⟨j, fr₁, s₁, h₁, h₂, -⟩ | ⟨k, fr₁, s₁, h₁, h₂, hag, hev⟩ |
      ⟨op, v, fr₁, s₁, k, k', h₁, h₂, -⟩ | ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩ <;> rw [h₂] at hsm ⊢ <;> rw [h₁]
    · exact (Corr.assigned hp hv hag (ha s v s₁ h₂)).follow hev
    · exact hsm.elim
    · exact hsm.elim
    · exact ⟨rfl, hag, hev⟩
    · exact hsm.elim
    · trivial
    · trivial
  · exact Sim.bind (h value hval) fun v hv fr s hs =>
      Corr.assigned hp hv hs fun r hr => absurd (pureIndexes_of_aliasRef hr) hpi

end Stilt.Sharing
