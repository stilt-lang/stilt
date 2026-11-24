import Stilt.Declarations

/-!
# Fixed points over the call graph

Consumption (values.consumed-parameters) and `once` parameters (modes.once-parameters) are
solved as fixed points over the call graph, as facts.inference solves implicit
effects: a round gives each parameter of the program a Boolean from the
previous round's, and rounds go on until nothing changes. A round of
consumption only adds parameters, and one of `once` only removes them, so as
many rounds as there are parameters reach the fixed point.

`repeat_fixed` proves it for a round that is monotone and holds only the
program's parameters, from no parameter, and `repeat_fixed_top` from every
parameter; `Stilt.Modes.Solved` applies them.
-/

namespace Stilt

/-- A Boolean for each parameter of the program's functions: of the function
with this name, at this position. -/
abbrev ParamSet := Name → Nat → Bool

/-- Every parameter that `A` holds, `B` holds. -/
def ParamSet.Le (A B : ParamSet) : Prop := ∀ g n, A g n = true → B g n = true

/-- No parameter. -/
def ParamSet.none : ParamSet := fun _ _ => false

theorem ParamSet.Le.refl (A : ParamSet) : A.Le A := fun _ _ => id

section

variable (step : ParamSet → ParamSet) (S : List (Name × Nat))

/-- How many of the parameters `S` a set holds. -/
def ParamSet.count (A : ParamSet) : Nat := S.countP fun gn => A gn.1 gn.2

theorem countP_lt {α : Type} {p q : α → Bool} :
    ∀ {l : List α}, (∀ x ∈ l, p x = true → q x = true) →
      (∃ x ∈ l, p x = false ∧ q x = true) →
      l.countP p < l.countP q
  | [], _, ⟨_, hx, _⟩ => nomatch hx
  | a :: l, hle, ⟨x, hx, hpx, hqx⟩ => by
    have hle' : ∀ y ∈ l, p y = true → q y = true :=
      fun y hy => hle y (List.mem_cons_of_mem a hy)
    rw [List.countP_cons, List.countP_cons]
    rcases List.mem_cons.1 hx with rfl | hx
    · simp only [hpx, hqx]
      have := List.countP_mono_left hle'
      simp only [Bool.false_eq_true, ↓reduceIte]
      omega
    · have := countP_lt hle' ⟨x, hx, hpx, hqx⟩
      by_cases hpa : p a = true
      · simp [hpa, hle a (List.mem_cons_self) hpa]
        omega
      · simp only [hpa, Bool.false_eq_true, ↓reduceIte]
        split <;> omega

variable {step S}

/-- The rounds from no parameter: each holds what the previous one held. -/
theorem repeat_le (mono : ∀ A B, A.Le B → (step A).Le (step B)) :
    ∀ k, (Nat.repeat step k ParamSet.none).Le (Nat.repeat step (k + 1) ParamSet.none)
  | 0 => fun _ _ h => nomatch h
  | k + 1 => mono _ _ (repeat_le mono k)

/-- After `k` rounds, either the next changes nothing, or at least `k + 1` of
the parameters are held. -/
theorem repeat_stable_or (mono : ∀ A B, A.Le B → (step A).Le (step B))
    (supp : ∀ A g n, step A g n = true → (g, n) ∈ S) : ∀ k,
    Nat.repeat step (k + 1) ParamSet.none = Nat.repeat step k ParamSet.none ∨
      k + 1 ≤ (Nat.repeat step (k + 1) ParamSet.none).count S := by
  intro k
  induction k with
  | zero =>
    show step ParamSet.none = ParamSet.none ∨ 1 ≤ (step ParamSet.none).count S
    by_cases h : ∃ g n, step ParamSet.none g n = true
    · obtain ⟨g, n, h⟩ := h
      have := countP_lt (p := fun gn => ParamSet.none gn.1 gn.2)
        (q := fun gn => step ParamSet.none gn.1 gn.2) (l := S) (fun _ _ h => nomatch h)
        ⟨(g, n), supp _ _ _ h, rfl, h⟩
      exact .inr (Nat.succ_le_of_lt (Nat.lt_of_le_of_lt (Nat.zero_le _) this))
    · refine .inl (funext fun g => funext fun n => ?_)
      cases hs : step ParamSet.none g n
      · rfl
      · exact absurd ⟨g, n, hs⟩ h
  | succ k ih =>
    by_cases heq : Nat.repeat step (k + 2) ParamSet.none = Nat.repeat step (k + 1) ParamSet.none
    · exact .inl heq
    · refine .inr ?_
      rcases ih with ih | ih
      · exact absurd (congrArg step ih) heq
      · have hle := repeat_le mono (k + 1)
        obtain ⟨g, n, hne⟩ : ∃ g n, Nat.repeat step (k + 2) ParamSet.none g n ≠
            Nat.repeat step (k + 1) ParamSet.none g n :=
          Classical.byContradiction fun h =>
            heq (funext fun g => funext fun n =>
              Classical.byContradiction fun h' => h ⟨g, n, h'⟩)
        have hold : Nat.repeat step (k + 1) ParamSet.none g n = false := by
          cases h : Nat.repeat step (k + 1) ParamSet.none g n
          · rfl
          · exact absurd ((hle g n h).trans h.symm) hne
        have hnew : Nat.repeat step (k + 2) ParamSet.none g n = true := by
          cases h : Nat.repeat step (k + 2) ParamSet.none g n
          · exact absurd (h.trans hold.symm) hne
          · rfl
        have := countP_lt (l := S) (fun gn _ h => hle gn.1 gn.2 h)
          ⟨(g, n), supp _ _ _ hnew, hold, hnew⟩
        simp only [ParamSet.count] at ih ⊢
        omega

/-- **The rounds reach the fixed point.** A round that only adds parameters
when it is given more, and holds only parameters of `S`, changes nothing after
as many rounds as `S` has parameters, and one more. -/
theorem repeat_fixed (mono : ∀ A B, A.Le B → (step A).Le (step B))
    (supp : ∀ A g n, step A g n = true → (g, n) ∈ S) :
    step (Nat.repeat step (S.length + 1) ParamSet.none) =
      Nat.repeat step (S.length + 1) ParamSet.none := by
  rcases repeat_stable_or mono supp S.length with h | h
  · exact congrArg step h
  · exact absurd (Nat.le_trans h List.countP_le_length) (by omega)

/-- Every parameter. -/
def ParamSet.all : ParamSet := fun _ _ => true

/-- The rounds from every parameter: each holds no more than the previous
one. -/
theorem repeat_ge (mono : ∀ A B, A.Le B → (step A).Le (step B)) :
    ∀ k, (Nat.repeat step (k + 1) ParamSet.all).Le (Nat.repeat step k ParamSet.all)
  | 0 => fun _ _ _ => rfl
  | k + 1 => mono _ _ (repeat_ge mono k)

/-- A parameter that one round from every parameter drops and the previous
held, which is one of `S`. -/
theorem repeat_drop (mono : ∀ A B, A.Le B → (step A).Le (step B))
    (supp : ∀ A g n, step A g n = true → (g, n) ∈ S) (k : Nat)
    (hne : Nat.repeat step (k + 2) ParamSet.all ≠ Nat.repeat step (k + 1) ParamSet.all) :
    (Nat.repeat step (k + 2) ParamSet.all).count S <
      (Nat.repeat step (k + 1) ParamSet.all).count S := by
  have hle := repeat_ge mono (k + 1)
  obtain ⟨g, n, hne⟩ : ∃ g n, Nat.repeat step (k + 2) ParamSet.all g n ≠
      Nat.repeat step (k + 1) ParamSet.all g n :=
    Classical.byContradiction fun h =>
      hne (funext fun g => funext fun n => Classical.byContradiction fun h' => h ⟨g, n, h'⟩)
  have hnew : Nat.repeat step (k + 2) ParamSet.all g n = false := by
    cases h : Nat.repeat step (k + 2) ParamSet.all g n
    · rfl
    · exact absurd ((hle g n h).symm ▸ h) hne
  have hold : Nat.repeat step (k + 1) ParamSet.all g n = true := by
    cases h : Nat.repeat step (k + 1) ParamSet.all g n
    · exact absurd (hnew.trans h.symm) hne
    · rfl
  exact countP_lt (l := S) (fun gn _ h => hle gn.1 gn.2 h) ⟨(g, n), supp _ _ _ hold, hnew, hold⟩

/-- After `k + 1` rounds from every parameter, either the next changes
nothing, or at most `S.length - (k + 1)` of the parameters are held. -/
theorem repeat_stable_or_top (mono : ∀ A B, A.Le B → (step A).Le (step B))
    (supp : ∀ A g n, step A g n = true → (g, n) ∈ S) : ∀ k,
    Nat.repeat step (k + 2) ParamSet.all = Nat.repeat step (k + 1) ParamSet.all ∨
      (Nat.repeat step (k + 2) ParamSet.all).count S + (k + 1) ≤ S.length := by
  intro k
  induction k with
  | zero =>
    show Nat.repeat step 2 ParamSet.all = Nat.repeat step 1 ParamSet.all ∨
      (Nat.repeat step 2 ParamSet.all).count S + 1 ≤ S.length
    by_cases heq : Nat.repeat step 2 ParamSet.all = Nat.repeat step 1 ParamSet.all
    · exact .inl heq
    · have h₁ : (Nat.repeat step 2 ParamSet.all).count S <
          (Nat.repeat step 1 ParamSet.all).count S := repeat_drop mono supp 0 heq
      have h₂ : (Nat.repeat step 1 ParamSet.all).count S ≤ S.length := List.countP_le_length
      exact .inr (by omega)
  | succ k ih =>
    show Nat.repeat step (k + 3) ParamSet.all = Nat.repeat step (k + 2) ParamSet.all ∨
      (Nat.repeat step (k + 3) ParamSet.all).count S + (k + 2) ≤ S.length
    by_cases heq : Nat.repeat step (k + 3) ParamSet.all = Nat.repeat step (k + 2) ParamSet.all
    · exact .inl heq
    · rcases ih with ih | ih
      · exact absurd (congrArg step ih) heq
      · have h₁ : (Nat.repeat step (k + 3) ParamSet.all).count S <
            (Nat.repeat step (k + 2) ParamSet.all).count S := repeat_drop mono supp (k + 1) heq
        exact .inr (by omega)

/-- **The rounds reach the fixed point, from every parameter.** A round that
holds no fewer parameters when it is given more, and holds only parameters of
`S`, changes nothing after as many rounds as `S` has parameters, and one
more. -/
theorem repeat_fixed_top (mono : ∀ A B, A.Le B → (step A).Le (step B))
    (supp : ∀ A g n, step A g n = true → (g, n) ∈ S) :
    step (Nat.repeat step (S.length + 1) ParamSet.all) =
      Nat.repeat step (S.length + 1) ParamSet.all := by
  rcases repeat_stable_or_top mono supp S.length with h | h
  · exact h
  · omega

end

end Stilt
