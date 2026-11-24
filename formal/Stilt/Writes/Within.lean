import Stilt.Writes.Scopes

/-!
# The end of a scope

Running the rest of a block with a binding, in both models, ends with states
that agree. The end of a value's scope frees its location in both; the end
of a writable binding's scope writes the copy model's part back, which gives
the window model's storage (projections.what-view-writes). The value the block gives still
agrees if it reads nothing the binding names, which views.escaping checks
(E0422).
-/

namespace Stilt.Writes

open Stilt.Views (Store bounded slice cell source Pointwise ExceptAgree Agree)

/-- What the scope of a binding of `x` ends with, from the window state `s₁`:
states that agree, a step under the names `F` frozen around it, and, if no
source in `Sb` is named `x`, a value that agrees, which `Sb` covers, with the
facts of `Post.pend` for a view that writes. -/
structure Closed (F Sb : List Name) (Pb : Prop) (x : Name) (s₁ sw sc : WState) (bw bc : WVal) :
    Prop where
  states : StateAgrees sw sc
  steps : Steps F s₁ sw
  value : (∀ y ∈ Sb, y ≠ x) → Agrees sw.store bw bc ∧
    (∀ ℓ π a b, bw = .window ℓ π a b → Cover Sb s₁.env ℓ) ∧ (Pb → Pending F s₁.env bw bc)

/-- The environment of the copy state, when the window state's has a binding
on top. -/
theorem EnvAgrees.cons_inv {sw sc : Store} {x : Name} {b : WBinding}
    {E Ec : List (Name × WBinding)} (h : EnvAgrees sw sc ((x, b) :: E) Ec) :
    ∃ c Ec', Ec = (x, c) :: Ec' ∧ BAgrees sw sc b c ∧ EnvAgrees sw sc E Ec' := by
  cases h with
  | cons hab hrest =>
    rename_i c Ec'
    obtain ⟨y, c⟩ := c
    obtain ⟨hy, hbc⟩ := hab
    simp only at hy
    subst hy
    exact ⟨c, Ec', rfl, hbc, hrest⟩

/-- A guard around a binding holds in its scope, where its name is hidden. -/
theorem Guarded.push {F F' : List Name} {env : List (Name × WBinding)} {x : Name}
    {b : WBinding} {ℓ : Nat} (h : Guarded F env ℓ) (hb : ¬Changes b ℓ)
    (hF : ∀ z ∈ F, z ≠ x → z ∈ F') : Guarded F' ((x, b) :: env) ℓ := fun z b' hz hc => by
  by_cases hzx : z = x
  · subst hzx
    simp only [List.lookup_cons_self, Option.some.injEq] at hz
    exact absurd (hz ▸ hc) hb
  · rw [lookup_cons_ne hzx] at hz
    exact hF z (h z b' hz hc) hzx

/-- A value agrees in a store that is the same where its window reads. -/
theorem Agrees.congr {st st' : Store} {rw rc : WVal} (h : Agrees st rw rc)
    (hs : ∀ ℓ π a c, rw = .window ℓ π a c → st'[ℓ]? = st[ℓ]?) : Agrees st' rw rc := by
  cases rw <;> cases rc <;> simp only [Agrees] at h ⊢
  · exact h
  · rw [part_congr _ _ _ (hs _ _ _ _ rfl)]
    exact h
  · rw [part_congr _ _ _ (hs _ _ _ _ rfl)]
    exact h

theorem cell_some {st : Store} {ℓ : Nat} {v : Value} (h : cell st ℓ = .ok v) :
    st[ℓ]? = some (some v) := by
  unfold cell at h
  split at h
  · cases h
    assumption
  · cases h

/-- The window state's store after the end of a scope, from the window state
`s₁` before its binding: guarded locations as they were. -/
theorem Steps.close {F : List Name} {s₁ : WState} {st : Store}
    (hgrow : s₁.store.length ≤ st.length)
    (hkeep : ∀ ℓ, Guarded F s₁.env ℓ → ℓ < s₁.store.length → st[ℓ]? = s₁.store[ℓ]?) :
    Steps F s₁ ⟨s₁.env, st⟩ :=
  ⟨rfl, hgrow, hkeep⟩

/-- The end of a scope, from the post of the rest of its block. -/
theorem Closed.of_post {R W S Sb : List Name} {Pb : Prop} {w : Bool} {x : Name}
    {b : WBinding} {s₁ sc₁ s₀ s₂ sc₂ : WState} {bw bc : WVal} (hst : StateAgrees s₁ sc₁)
    (henv : s₀.env = (x, b) :: s₁.env)
    (hb : Fresh (R ++ W) S w s₁ b) (hgrow : s₁.store.length ≤ s₀.store.length)
    (hsame : ∀ ℓ, ℓ < s₁.store.length → s₀.store[ℓ]? = s₁.store[ℓ]?)
    (hp : Post (hide (readsIn w S R) x ++ hide (writesIn w S W) x) Sb Pb s₀ s₂ sc₂ bw bc) :
    ExceptAgree (fun sw sc => Closed (R ++ W) Sb Pb x s₁ sw sc bw bc) s₂.unbind sc₂.unbind := by
  have h₂env : s₂.env = (x, b) :: s₁.env := hp.steps.env.trans henv
  obtain ⟨c, Ec, hEc, hbc, hrest⟩ := (h₂env ▸ hp.states.env :).cons_inv
  have hgrow₂ := Nat.le_trans hgrow hp.steps.grows
  -- A guarded location of `s₁` is one the binding doesn't change.
  have hgc : ∀ ℓ, Guarded (R ++ W) s₁.env ℓ → ℓ < s₁.store.length → ¬Changes b ℓ := by
    intro ℓ hg hl hc
    cases b with
    | loc ℓ₀ => exact absurd hb.2 (by have : ℓ₀ = ℓ := hc; omega)
    | view _ => exact hc
    | writes r =>
      obtain ⟨-, ℓ₀, _, _, _, rfl, -, -, y, hy, hyF⟩ := hb
      exact hg.ne hy rfl hyF hc.symm
  have hkeep : ∀ ℓ, Guarded (R ++ W) s₁.env ℓ → ℓ < s₁.store.length →
      s₂.store[ℓ]? = s₁.store[ℓ]? := fun ℓ hg hl => by
    rw [hp.steps.preserves ℓ (henv ▸ hg.push (hgc ℓ hg hl) fun z hz hzx => mem_frozen hz hzx)
      (Nat.lt_of_lt_of_le hl hgrow), hsame ℓ hl]
  -- The value of the block reads nothing the binding changes.
  have hvalue : (∀ y ∈ Sb, y ≠ x) → (∀ ℓ π a c, bw = .window ℓ π a c → ¬Changes b ℓ) ∧
      (∀ ℓ π a c, bw = .window ℓ π a c → Cover Sb s₁.env ℓ) ∧
      (Pb → Pending (R ++ W) s₁.env bw bc) := by
    intro hroot
    have hnc : ∀ ℓ π a c, bw = .window ℓ π a c → ¬Changes b ℓ := fun ℓ π a c he hc =>
      hroot x (hp.within ℓ π a c he x b (henv ▸ List.mem_cons_self) hc) rfl
    refine ⟨hnc, fun ℓ π a c he => (henv ▸ hp.within ℓ π a c he).tail, fun hP => ?_⟩
    obtain ⟨part, ℓ, π, a, c, rfl, rfl, hal, y, hy, hyF⟩ := hp.pend hP
    have hyx : y ≠ x := fun he => by
      subst he
      rw [henv] at hy
      simp only [List.lookup_cons_self, Option.some.injEq] at hy
      exact hnc ℓ π a c rfl (hy ▸ rfl)
    rw [henv, lookup_cons_ne hyx] at hy
    exact ⟨part, ℓ, π, a, c, rfl, rfl, fun z b' hz => hal z b' (henv ▸ List.mem_cons_of_mem _ hz),
      y, hy, fun hm => hyF (mem_frozen hm hyx)⟩
  have hoff : ∀ ℓ, (∀ y b', (y, b') ∈ s₁.env → ¬Targets b' ℓ) → ¬Targets b ℓ →
      s₂.store[ℓ]? = sc₂.store[ℓ]? := fun ℓ hu ht => hp.states.off ℓ fun y b' hy => by
    rw [h₂env] at hy
    rcases List.mem_cons.1 hy with hy | hy
    · cases hy
      exact ht
    · exact hu y b' hy
  unfold WState.unbind
  rw [h₂env, hEc]
  cases b with
  | loc ℓ₀ =>
    cases c <;> simp only [BAgrees] at hbc
    subst hbc
    have hne : ∀ y b' ℓ, (y, b') ∈ s₁.env → Refers b' ℓ → ℓ ≠ ℓ₀ := fun y b' ℓ hy hr he => by
      have := hst.lt hy (.inr hr)
      have := hb.2
      omega
    refine ⟨⟨by simp [hp.states.length], Pointwise.imp_left (fun e c' he hp' => ⟨hp'.1,
      hp'.2.congr fun ℓ hr => ⟨List.getElem?_set_ne (hne _ _ ℓ he hr).symm,
        List.getElem?_set_ne (hne _ _ ℓ he hr).symm⟩⟩) hrest, fun ℓ hu => ?_,
      fun y ℓ hy => ?_⟩, Steps.close (by simpa using hgrow₂) fun ℓ hg hl => ?_, fun hroot => ?_⟩
    · by_cases he : ℓ = ℓ₀
      · subst he
        exact Writes.getElem?_set_eq _ hp.states.length
      · simp only [List.getElem?_set_ne (Ne.symm he)]
        exact hoff ℓ hu fun ht => ht.elim
    · simpa using Nat.lt_of_lt_of_le (hst.locs y ℓ hy) hgrow₂
    · have : ℓ ≠ ℓ₀ := fun he => absurd hb.2 (by omega)
      simp only [List.getElem?_set_ne this.symm]
      exact hkeep ℓ hg hl
    · obtain ⟨hnc, hcov, hpend⟩ := hvalue hroot
      exact ⟨hp.agrees.congr fun ℓ π a c he => List.getElem?_set_ne fun h =>
        hnc ℓ π a c he (show ℓ₀ = ℓ from h), hcov, hpend⟩
  | view r =>
    obtain ⟨r', rfl, -⟩ := hbc.view_inv
    refine ⟨⟨hp.states.length, hrest, fun ℓ hu => hoff ℓ hu fun ht => ht.elim,
      fun y ℓ hy => Nat.lt_of_lt_of_le (hst.locs y ℓ hy) hgrow₂⟩,
      Steps.close hgrow₂ hkeep, fun hroot => ?_⟩
    obtain ⟨-, hcov, hpend⟩ := hvalue hroot
    exact ⟨hp.agrees, hcov, hpend⟩
  | writes r =>
    obtain ⟨ℓ₀, π, a, b, part, rfl, rfl, c₀, c₀', hc, hc', hr⟩ := hbc.writes_inv
    obtain ⟨-, _, _, _, _, he, -, hal, -⟩ := hb
    cases he
    have hne : ∀ y b' ℓ, (y, b') ∈ s₁.env → Refers b' ℓ → ℓ ≠ ℓ₀ :=
      fun y b' ℓ hy hr' he => hal y b' hy (he ▸ hr')
    simp only [release, hc, hr]
    refine ⟨⟨by simp [hp.states.length], Pointwise.imp_left (fun e c' he hp' => ⟨hp'.1,
      hp'.2.congr fun ℓ hr' => ⟨rfl, List.getElem?_set_ne (hne _ _ ℓ he hr').symm⟩⟩) hrest,
      fun ℓ hu => ?_, fun y ℓ hy => Nat.lt_of_lt_of_le (hst.locs y ℓ hy) hgrow₂⟩,
      Steps.close hgrow₂ hkeep, fun hroot => ?_⟩
    · by_cases he : ℓ = ℓ₀
      · subst he
        rw [cell_some hc', List.getElem?_set_self (Views.cell_lt hc)]
      · simp only [List.getElem?_set_ne (Ne.symm he)]
        exact hoff ℓ hu fun ht => he ht.symm
    · obtain ⟨-, hcov, hpend⟩ := hvalue hroot
      exact ⟨hp.agrees, hcov, hpend⟩

/-- Running the rest of a block with `x` bound to values that agree keeps the
simulation, when the rest of the block keeps it from every state that the
binding gives. -/
theorem Agree.within {Γ : Sources} {R W S Sb : List Name} {Pb : Prop} {w : Bool} {x : Name}
    {mw mc : Eval WState WVal} {s₁ sc₁ : WState} {rw rc : WVal} (hst : StateAgrees s₁ sc₁)
    (hs : InScope Γ R W s₁.env) (hag : Agrees s₁.store rw rc)
    (hwin : ∀ ℓ π a b, rw = .window ℓ π a b → Cover S s₁.env ℓ)
    (hpend : w = true → Pending (R ++ W) s₁.env rw rc)
    (hbody : ∀ sw sc, StateAgrees sw sc →
      InScope ((x, held w x S) :: Γ) (hide (readsIn w S R) x) (hide (writesIn w S W) x) sw.env →
      Agree (Post (hide (readsIn w S R) x ++ hide (writesIn w S W) x) Sb Pb sw) (mw sw) (mc sc)) :
    Agree (fun sw sc bw bc => Closed (R ++ W) Sb Pb x s₁ sw sc bw bc)
      (Run.within w x rw mw s₁) (Run.within w x rc mc sc₁) := by
  obtain ⟨hst', b, henv, hfresh, hgrow, hsame⟩ := hst.bind hag hwin hpend x
  have hscope : InScope ((x, held w x S) :: Γ) (hide (readsIn w S R) x)
      (hide (writesIn w S W) x) (s₁.bind w x rw).env := by
    rw [henv]
    exact hs.push hst hfresh
  have hb := hbody _ _ hst' hscope
  unfold Run.within
  revert hb
  cases mw (s₁.bind w x rw) <;> cases mc (sc₁.bind w x rc) <;> intro hb <;>
    simp only [Agree, Agree.relation, Outcome.Rel] at hb ⊢ <;> try exact hb
  rename_i bw s₂ bc sc₂
  have hcl := Closed.of_post hst henv hfresh hgrow hsame hb
  revert hcl
  cases s₂.unbind <;> cases sc₂.unbind <;> intro hcl <;> simp only [ExceptAgree] at hcl <;>
    first | exact hcl.elim | exact hcl | (subst hcl; rename_i f; cases f <;> first | exact trivial | rfl)

end Stilt.Writes
