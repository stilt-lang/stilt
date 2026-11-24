import Stilt.Views.Scopes

/-!
# The end of a scope

Running the rest of a block with a binding, in both models, ends with states
that agree and a step under the reads around the block. The scope's end frees
the binding's location, so the value the block gives still agrees only if it
reads no source that the binding names, which views.escaping checks
(E0422).
-/

namespace Stilt.Views

/-- What the scope of a binding of `x` ends with, from the window state `s₁`:
states that agree, a step under the reads `R` around it, and, if no source in
`Sb` is named `x`, a value that agrees and that `Sb` covers. -/
structure Closed (R Sb : List Shape) (x : Name) (s₁ sw sc : VState) (bw bc : RVal) : Prop where
  states : StateAgrees sw sc
  steps : Steps R s₁ sw
  value : (∀ y ∈ Sb, y.root ≠ x) → Agrees sw.store bw bc ∧ bw.Within Sb s₁.env

theorem freeing_length (b : Binding) (store : Store) : (freeing b store).length = store.length := by
  cases b <;> simp [freeing]

theorem freeing_agrees {store : Store} {b c : Binding} (h : BAgrees store b c) (store' : Store) :
    freeing c store' = freeing b store' := by
  cases b <;> cases c <;> try exact False.elim h
  · cases (show _ = _ from h)
    rfl
  · rfl

/-- The environment of the copy state, when the window state's has a binding
on top. -/
theorem EnvAgrees.cons_inv {store : Store} {x : Name} {b : Binding}
    {E Ec : List (Name × Binding)} (h : EnvAgrees store ((x, b) :: E) Ec) :
    ∃ c Ec', Ec = (x, c) :: Ec' ∧ BAgrees store b c ∧ EnvAgrees store E Ec' := by
  cases h with
  | cons hab hrest =>
    rename_i c Ec'
    obtain ⟨y, c⟩ := c
    obtain ⟨hy, hbc⟩ := hab
    simp only at hy
    subst hy
    exact ⟨c, Ec', rfl, hbc, hrest⟩

theorem Covered.tail {S : List Shape} {x : Name} {b : Binding} {env : List (Name × Binding)}
    {ℓ : Nat} {π : Path} (h : Covered S ((x, b) :: env) ℓ π) : Covered S env ℓ π :=
  fun y hy => h y (List.mem_cons_of_mem _ hy)

theorem RVal.Within.tail {S : List Shape} {x : Name} {b : Binding}
    {env : List (Name × Binding)} {r : RVal} (h : r.Within S ((x, b) :: env)) : r.Within S env := by
  cases r <;> first | trivial | exact Covered.tail h

/-- The end of a scope, from the post of the rest of its block. -/
theorem Closed.of_post {R S Sb : List Shape} {x : Name} {b : Binding} {s₁ sc₁ s₀ s₂ sc₂ : VState}
    {bw bc : RVal} (hst : StateAgrees s₁ sc₁) (henv : s₀.env = (x, b) :: s₁.env)
    (hfresh : ∀ ℓ, b = .loc ℓ → s₁.store.length ≤ ℓ)
    (hgrow : s₁.store.length ≤ s₀.store.length)
    (hsame : ∀ ℓ π, ℓ < s₁.store.length → source s₀.store ℓ π = source s₁.store ℓ π)
    (hp : Post (hide (S ++ R) x) Sb s₀ s₂ sc₂ bw bc) :
    Closed R Sb x s₁ s₂.unbind sc₂.unbind bw bc := by
  have hne : ∀ ℓ, ℓ < s₁.store.length → b ≠ .loc ℓ := fun ℓ hℓ he =>
    Nat.lt_irrefl _ (Nat.lt_of_lt_of_le hℓ (hfresh ℓ he))
  have h₂env : s₂.env = (x, b) :: s₁.env := hp.steps.env.trans henv
  obtain ⟨c, Ec, hEc, hbc, hrest⟩ := (h₂env ▸ hp.states.env :).cons_inv
  rw [unbind_cons h₂env, unbind_cons hEc, freeing_agrees hbc, ← hp.states.store]
  have hlen : s₁.store.length ≤ (freeing b s₂.store).length := by
    rw [freeing_length]
    exact Nat.le_trans hgrow hp.steps.grows
  refine ⟨⟨rfl, hrest.congr fun y ℓ π a d hy => ?_, fun y ℓ hy => ?_⟩, ⟨rfl, hlen, ?_⟩, ?_⟩
  · exact source_freeing π (hne ℓ (hst.env.window_lt hy))
  · exact Nat.lt_of_lt_of_le (hst.locs y ℓ hy) hlen
  · intro ℓ π hg hℓ
    have hg' : Guarded (hide (S ++ R) x) s₀.env ℓ π := henv ▸ hg.cons (hne ℓ hℓ)
    rw [source_freeing π (hne ℓ hℓ), hp.steps.preserves ℓ π hg' (Nat.lt_of_lt_of_le hℓ hgrow),
      hsame ℓ π hℓ]
  · intro hroot
    have hwin : bw.Within Sb ((x, b) :: s₁.env) := henv ▸ hp.within
    refine ⟨Agrees.congr hp.agrees fun ℓ π a d he => source_freeing π fun hb => ?_, hwin.tail⟩
    subst he hb
    exact hroot _ (hwin x List.mem_cons_self) rfl

/-- Running the rest of a block with `x` bound to values that agree keeps the
simulation, when the rest of the block keeps it from every state that the
binding gives. -/
theorem Agree.within {Γ : Sources} {R S Sb : List Shape} {x : Name}
    {mw mc : Eval VState RVal} {s₁ sc₁ : VState} {rw rc : RVal}
    (hst : StateAgrees s₁ sc₁) (hscope : InScope Γ R s₁.env)
    (hag : Agrees s₁.store rw rc) (hwin : rw.Within S s₁.env)
    (hbody : ∀ sw sc, StateAgrees sw sc → InScope ((x, S) :: Γ) (hide (S ++ R) x) sw.env →
      Agree (Post (hide (S ++ R) x) Sb sw) (mw sw) (mc sc)) :
    Agree (Closed R Sb x s₁) (Run.within x rw mw s₁) (Run.within x rc mc sc₁) := by
  obtain ⟨hst', b, henv, hfresh, hview, hgrow, hsame⟩ := hst.bind hag x
  have hscope' : InScope ((x, S) :: Γ) (hide (S ++ R) x) (s₁.bind x rw).env := by
    rw [henv]
    refine hscope.push hst.locs (fun _ _ _ _ _ hy => hst.env.window_lt hy) hfresh
      fun ℓ π a c hb => ?_
    rw [hview ℓ π a c hb] at hwin
    exact hwin
  have hb := hbody _ _ hst' hscope'
  unfold Run.within
  revert hb
  cases mw (s₁.bind x rw) <;> cases mc (sc₁.bind x rc) <;> intro hb <;>
    simp only [Agree, Agree.relation, Outcome.Rel] at hb ⊢ <;> try exact hb
  exact Closed.of_post hst henv hfresh hgrow hsame hb

end Stilt.Views
