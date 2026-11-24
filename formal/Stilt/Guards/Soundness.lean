import Stilt.Guards.Covers

/-!
# Bindings and evaluation

Every way in which a pattern of type `τ` binding `Δ` matches a value of type
`τ` binds the names of `Δ` to values of their types and nothing else
(`Pat.ways_agree`), so a guard and a body typed with `Δ` in scope evaluate,
in those bindings, to values of their types (`eval_sound`). An irrefutable
pattern matches every value of its type (`Pat.irrefutable_matches`).
-/

namespace Stilt.Guards

theorem lookup_append {β : Type} (x : Name) : ∀ (l₁ l₂ : List (Name × β)),
    (l₁ ++ l₂).lookup x = (l₁.lookup x).or (l₂.lookup x)
  | [], _ => rfl
  | (y, b) :: l₁, l₂ => by
    simp only [List.cons_append, List.lookup]
    split <;> simp [lookup_append x l₁ l₂]

theorem Agree.nil : Agree [] [] := ⟨fun _ _ h => (nomatch h), fun _ _ => rfl⟩

theorem Agree.single {x : Name} {v : Val} {τ : Ty} (hv : ValTy v τ) : Agree [(x, v)] [(x, τ)] := by
  refine ⟨fun y σ h => ?_, fun y h => ?_⟩
  · simp only [List.lookup] at h ⊢
    split at h <;> simp_all
  · simp only [List.lookup] at h ⊢
    split at h <;> simp_all

theorem Agree.append {w₁ w₂ : Env} {Δ₁ Δ₂ : Ctx} (h₁ : Agree w₁ Δ₁) (h₂ : Agree w₂ Δ₂) :
    Agree (w₁ ++ w₂) (Δ₁ ++ Δ₂) := by
  refine ⟨fun x τ h => ?_, fun x h => ?_⟩
  · rw [lookup_append] at h ⊢
    cases hx : Δ₁.lookup x with
    | some σ =>
      rw [hx] at h
      cases h
      obtain ⟨v, hv, hvt⟩ := h₁.bound x _ hx
      exact ⟨v, by simp [hv], hvt⟩
    | none =>
      rw [hx] at h
      rw [h₁.unbound x hx]
      exact h₂.bound x τ h
  · rw [lookup_append] at h ⊢
    cases hx : Δ₁.lookup x with
    | some _ => rw [hx] at h; cases h
    | none =>
      rw [hx] at h
      rw [h₁.unbound x hx, h₂.unbound x h]
      rfl

/-- The bindings of a way, in front of variables of a context's types. -/
theorem Agree.env {w : Env} {Δ : Ctx} {ρ : Env} {Γ : Ctx} (hw : Agree w Δ) (hρ : EnvOk ρ Γ) :
    EnvOk (w ++ ρ) (Δ ++ Γ) := by
  intro x τ h
  rw [lookup_append] at h ⊢
  cases hx : Δ.lookup x with
  | some σ =>
    rw [hx] at h
    cases h
    obtain ⟨v, hv, hvt⟩ := hw.bound x _ hx
    exact ⟨v, by simp [hv], hvt⟩
  | none =>
    rw [hx] at h
    rw [hw.unbound x hx]
    exact hρ x τ h

theorem waysAll_length : ∀ {ps : List Pat} {vs : List Val} {w : Env}, w ∈ Pat.waysAll ps vs →
    ps.length = vs.length := by
  intro ps vs w hw
  have : RowMatches ps vs := List.ne_nil_of_mem hw
  exact rowMatches_length this

/-- The first elements of a list of values of a type. -/
theorem valsTy_take {us : List Val} {τ : Ty} (h : ∀ u ∈ us, ValTy u τ) {n : Nat} (hn : n ≤ us.length) :
    ValsTy (us.take n) (List.replicate n τ) := by
  have := ValsTy.replicate (us := us.take n) fun u hu => h u (List.mem_of_mem_take hu)
  rwa [List.length_take, Nat.min_eq_left hn] at this

mutual

theorem Pat.ways_agree : ∀ (p : Pat) {τ : Ty} {Δ : Ctx} {v : Val} {w : Env},
    PatTy p τ Δ → ValTy v τ → w ∈ p.ways v → Agree w Δ
  | .wild, _, _, _, _, .wild, _, hw => by
    simp only [Pat.ways, List.mem_singleton] at hw; subst hw; exact Agree.nil
  | .bind _, _, _, _, _, .bind, hv, hw => by
    simp only [Pat.ways, List.mem_singleton] at hw; subst hw; exact Agree.single hv
  | .int _, _, _, _, _, .int, .int, hw | .bool _, _, _, _, _, .bool, .bool, hw => by
    simp only [Pat.ways] at hw; split at hw <;> simp_all [Agree.nil]
  | .unit, _, _, _, _, .unit, .unit, hw | .none, _, _, _, _, .none, .none, hw => by
    simp only [Pat.ways, List.mem_singleton] at hw; subst hw; exact Agree.nil
  | .none, _, _, _, _, .none, .some _, hw => by simp [Pat.ways] at hw
  | .const _ _, _, _, _, _, .const _, _, hw => by
    simp only [Pat.ways] at hw; split at hw <;> simp_all [Agree.nil]
  | .tuple ps, _, _, _, _, .tuple hps, .tuple hus, hw => by
    simp only [Pat.ways] at hw
    exact Pat.waysAll_agree ps hps hus hw
  | .some p, _, _, _, _, .some hp, .some hu, hw => by
    simp only [Pat.ways] at hw
    exact Pat.ways_agree p hp hu hw
  | .some _, _, _, _, _, .some _, .none, hw => by simp [Pat.ways] at hw
  | .list ps, _, _, _, _, .list hps, .list hus, hw => by
    simp only [Pat.ways] at hw
    have hl := waysAll_length hw
    have := ValsTy.replicate hus
    rw [← hl] at this
    exact Pat.waysAll_agree ps hps this hw
  | .prefix ps _, _, _, _, _, .prefix hps, .list hus, hw => by
    simp only [Pat.ways] at hw
    split at hw
    · obtain ⟨w', hw', rfl⟩ := List.mem_map.1 hw
      have := Pat.waysAll_agree ps hps (valsTy_take hus (by assumption)) hw'
      simpa [Pat.rest] using this
    · simp at hw
  | .prefix ps _, _, _, _, _, .prefixRest hps, .list hus, hw => by
    simp only [Pat.ways] at hw
    split at hw
    · obtain ⟨w', hw', rfl⟩ := List.mem_map.1 hw
      have := Pat.waysAll_agree ps hps (valsTy_take hus (by assumption)) hw'
      exact this.append (Agree.single (.list fun u hu => hus u (List.mem_of_mem_drop hu)))
    · simp at hw
  | .or p q, _, _, _, _, .or hp hq hΔ, hv, hw => by
    simp only [Pat.ways, List.mem_append] at hw
    rcases hw with hw | hw
    · exact Pat.ways_agree p hp hv hw
    · have h := Pat.ways_agree q hq hv hw
      exact ⟨fun x τ hx => h.bound x τ (by rw [hΔ]; exact hx),
        fun x hx => h.unbound x (by rw [hΔ]; exact hx)⟩

theorem Pat.waysAll_agree : ∀ (ps : List Pat) {τs : List Ty} {Δ : Ctx} {vs : List Val} {w : Env},
    PatsTy ps τs Δ → ValsTy vs τs → w ∈ Pat.waysAll ps vs → Agree w Δ
  | [], _, _, _, _, .nil, .nil, hw => by
    simp only [Pat.waysAll, List.mem_singleton] at hw; subst hw; exact Agree.nil
  | p :: ps, _, _, _, _, .cons hp hps, .cons hv hvs, hw => by
    simp only [Pat.waysAll, List.mem_flatMap, List.mem_map] at hw
    obtain ⟨w₁, hw₁, w₂, hw₂, rfl⟩ := hw
    exact (Pat.ways_agree p hp hv hw₁).append (Pat.waysAll_agree ps hps hvs hw₂)

end

/-- A well-typed expression evaluates, from variables of its context's types,
to a value of its type. -/
theorem eval_sound {Γ : Ctx} {e : Expr} {τ : Ty} (h : HasType Γ e τ) {ρ : Env} (hρ : EnvOk ρ Γ) :
    ∃ v out, eval ρ e = some (v, out) ∧ ValTy v τ := by
  induction h with
  | num => exact ⟨_, _, rfl, .int⟩
  | bool => exact ⟨_, _, rfl, .bool⟩
  | unit => exact ⟨_, _, rfl, .unit⟩
  | var hx =>
    obtain ⟨v, hv, hvt⟩ := hρ _ _ hx
    exact ⟨v, [], by simp [eval, hv], hvt⟩
  | add _ _ iha ihb =>
    obtain ⟨va, oa, ha, hta⟩ := iha
    obtain ⟨vb, ob, hb, htb⟩ := ihb
    cases hta; cases htb
    exact ⟨_, oa ++ ob, by simp only [eval, ha, hb] <;> rfl, .int⟩
  | lt _ _ iha ihb =>
    obtain ⟨va, oa, ha, hta⟩ := iha
    obtain ⟨vb, ob, hb, htb⟩ := ihb
    cases hta; cases htb
    exact ⟨.bool _, oa ++ ob, by simp only [eval, ha, hb] <;> rfl, .bool⟩
  | print _ _ iha ihb =>
    obtain ⟨va, oa, ha, _⟩ := iha
    obtain ⟨vb, ob, hb, htb⟩ := ihb
    exact ⟨vb, _, by simp only [eval, ha, hb] <;> rfl, htb⟩

mutual

/-- An irrefutable pattern matches every value of its type
(patterns.irrefutable-positions). -/
theorem Pat.irrefutable_matches : ∀ (p : Pat) {τ : Ty} {Δ : Ctx} {v : Val},
    PatTy p τ Δ → p.irrefutable = true → ValTy v τ → Matches p v
  | .wild, _, _, v, _, _, _ => Pat.isWild_matches rfl v
  | .bind _, _, _, v, _, _, _ => Pat.isWild_matches rfl v
  | .unit, _, _, _, .unit, _, .unit => by simp [Matches, Pat.ways]
  | .tuple ps, _, _, _, .tuple hps, hi, .tuple hus => by
    simp only [Pat.irrefutable] at hi
    have := Pat.allIrrefutable_matches ps hps hi hus
    simpa [Matches, Pat.ways, RowMatches] using this
  | .prefix [] _, _, _, _, _, _, .list _ => by
    simp [Matches, Pat.ways, Pat.waysAll]
  | .or p q, _, _, v, .or hp hq _, hi, hv => by
    simp only [Pat.irrefutable, Bool.or_eq_true] at hi
    simp only [Matches, Pat.ways, ne_eq, List.append_eq_nil_iff]
    rcases hi with hi | hi
    · exact fun h => Pat.irrefutable_matches p hp hi hv h.1
    · exact fun h => Pat.irrefutable_matches q hq hi hv h.2
  | .int _, _, _, _, _, hi, _ | .bool _, _, _, _, _, hi, _ | .const _ _, _, _, _, _, hi, _
  | .none, _, _, _, _, hi, _ | .some _, _, _, _, _, hi, _ | .list _, _, _, _, _, hi, _
  | .prefix (_ :: _) _, _, _, _, _, hi, _ => by simp [Pat.irrefutable] at hi

theorem Pat.allIrrefutable_matches : ∀ (ps : List Pat) {τs : List Ty} {Δ : Ctx} {vs : List Val},
    PatsTy ps τs Δ → Pat.allIrrefutable ps = true → ValsTy vs τs → RowMatches ps vs
  | [], _, _, _, .nil, _, .nil => rowMatches_nil
  | p :: ps, _, _, _, .cons hp hps, hi, .cons hv hvs => by
    simp only [Pat.allIrrefutable, Bool.and_eq_true] at hi
    exact rowMatches_cons.2
      ⟨Pat.irrefutable_matches p hp hi.1 hv, Pat.allIrrefutable_matches ps hps hi.2 hvs⟩

end

end Stilt.Guards
