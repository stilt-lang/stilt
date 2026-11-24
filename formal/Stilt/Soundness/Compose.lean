import Stilt.Soundness.Close

/-!
# Instantiation at run time

A use instantiates the row variables of a function with `s` (effects.inference),
and the body runs under the environment that `s` composes with the use's own
(`RowSubst.compose`). Reading the instantiated type under the use's
environment gives the type read under the composed one, up to equivalence,
when the use leaves every row of the type one `raise` label (effects.one-error-type): the label
that `Row.substRows` keeps is then the one every variable brings.
-/

namespace Stilt

theorem Row.substRows_eq (s : RowSubst) (ρ : Row) :
    ρ.substRows s = ⟨ρ.io || ρ.vars.any (fun v => (s.lookup v).any (·.io)),
      ρ.raise.map (Ty.substRows s) <|> ρ.vars.findSome? (fun v => (s.lookup v).bind (·.raise)),
      ρ.vars.flatMap (fun v => (s.lookup v).elim [v] (·.vars)),
      ρ.effects ++ ρ.vars.flatMap (fun v => (s.lookup v).elim [] (·.effects)), ρ.resume⟩ := by
  obtain ⟨io, raise, vars⟩ := ρ
  cases raise <;> rfl

section

variable {s : RowSubst} {ρ : Row}

/-- The label an instantiated row keeps is one of its labels. -/
theorem Row.raise_substRows_mem {F : Ty} (h : (ρ.substRows s).raise = some F) :
    F ∈ ρ.labels s := by
  rw [Row.substRows_eq] at h
  simp only [Row.labels, List.mem_append, List.mem_map, Option.mem_toList, List.mem_filterMap]
  cases hr : ρ.raise with
  | some E =>
    rw [hr] at h
    exact .inl ⟨E, rfl, Option.some.inj h⟩
  | none =>
    rw [hr] at h
    exact .inr (List.exists_of_findSome?_eq_some h)

/-- An instantiated row that has a label keeps one. -/
theorem Row.raise_substRows_isSome {G : Ty} (h : G ∈ ρ.labels s) :
    ∃ F, (ρ.substRows s).raise = some F := by
  rw [Row.substRows_eq]
  cases hr : ρ.raise with
  | some E => exact ⟨_, rfl⟩
  | none =>
    simp only [Row.labels, hr, Option.toList_none, List.map_nil, List.nil_append,
      List.mem_filterMap] at h
    obtain ⟨v, hv, hG⟩ := h
    cases hf : ρ.vars.findSome? (fun v => (s.lookup v).bind (·.raise)) with
    | some F => exact ⟨F, by simp⟩
    | none => exact absurd hG (by simp [List.findSome?_eq_none_iff.1 hf v hv])

theorem Row.mem_vars_substRows {w : Name} :
    w ∈ (ρ.substRows s).vars ↔ ∃ v ∈ ρ.vars, w ∈ (s.lookup v).elim [v] (·.vars) := by
  rw [Row.substRows_eq]
  simp

theorem Row.mem_effects_substRows {E : Name} :
    E ∈ (ρ.substRows s).effects ↔
      E ∈ ρ.effects ∨ ∃ v ∈ ρ.vars, E ∈ (s.lookup v).elim [] (·.effects) := by
  rw [Row.substRows_eq]
  simp

theorem Row.resume_substRows : (ρ.substRows s).resume = ρ.resume := by
  rw [Row.substRows_eq]

end

theorem RowSubst.mem_compose {s : RowSubst} {η : REnv} {v : Name} {x : STy} :
    x ∈ s.compose η v ↔ (s.lookup v = none ∧ x ∈ η v) ∨ ∃ σ, s.lookup v = some σ ∧ x ∈ σ.close η := by
  unfold RowSubst.compose
  cases s.lookup v <;> simp

/-- An instantiated row raises, read under the use's environment, what the row
raises under the composed one. -/
theorem Row.close_substRows_le {s : RowSubst} {η : REnv} {ρ : Row}
    (hE : ∀ E, ρ.raise = some E → ((E.substRows s).close η).Eqv (E.close (s.compose η))) :
    Covers ((ρ.substRows s).close η) (ρ.close (s.compose η)) := by
  refine Covers.of_forall fun x hx => ?_
  rcases Row.mem_close.1 hx with ⟨F, hF, rfl⟩ | ⟨w, hw, hx⟩ | ⟨E, hE, rfl⟩ | ⟨p, hp, rfl⟩
  · cases hr : ρ.raise with
    | some E =>
      rw [Row.substRows_eq, hr] at hF
      obtain rfl := Option.some.inj hF
      exact Has.of_mem_eqv (Row.mem_close.2 (.inl ⟨E, hr, rfl⟩)) (hE E hr)
    | none =>
      rw [Row.substRows_eq, hr] at hF
      obtain ⟨v, hv, hσ⟩ := List.exists_of_findSome?_eq_some hF
      cases hl : s.lookup v with
      | none => simp [hl] at hσ
      | some σ =>
        simp only [hl, Option.bind_some] at hσ
        exact Has.of_mem (Row.mem_close.2 (.inr (.inl ⟨v, hv, RowSubst.mem_compose.2
          (.inr ⟨σ, hl, Row.mem_close.2 (.inl ⟨F, hσ, rfl⟩)⟩)⟩)))
  · obtain ⟨v, hv, hwv⟩ := Row.mem_vars_substRows.1 hw
    refine Has.of_mem (Row.mem_close.2 (.inr (.inl ⟨v, hv, RowSubst.mem_compose.2 ?_⟩)))
    cases hl : s.lookup v with
    | none =>
      simp only [hl, Option.elim_none, List.mem_singleton] at hwv
      exact .inl ⟨rfl, hwv ▸ hx⟩
    | some σ =>
      simp only [hl, Option.elim_some] at hwv
      exact .inr ⟨σ, rfl, Row.mem_close.2 (.inr (.inl ⟨w, hwv, hx⟩))⟩
  · rcases Row.mem_effects_substRows.1 hE with hE | ⟨v, hv, hE⟩
    · exact Has.of_mem (Row.mem_close.2 (.inr (.inr (.inl ⟨E, hE, rfl⟩))))
    · cases hl : s.lookup v with
      | none => simp [hl] at hE
      | some σ =>
        simp only [hl, Option.elim_some] at hE
        exact Has.of_mem (Row.mem_close.2 (.inr (.inl ⟨v, hv, RowSubst.mem_compose.2
          (.inr ⟨σ, hl, Row.mem_close.2 (.inr (.inr (.inl ⟨E, hE, rfl⟩)))⟩)⟩)))
  · rw [Row.resume_substRows] at hp
    exact Has.of_mem (Row.mem_close.2 (.inr (.inr (.inr ⟨p, hp, rfl⟩))))

/-- A row raises, under the composed environment, what its instantiation
raises under the use's, when the use leaves it one `raise` label. -/
theorem Row.close_substRows_ge {s : RowSubst} {η : REnv} {ρ : Row} (hkeep : ρ.KeepsOneRaise s)
    (hE : ∀ E, ρ.raise = some E → ((E.substRows s).close η).Eqv (E.close (s.compose η))) :
    Covers (ρ.close (s.compose η)) ((ρ.substRows s).close η) := by
  refine Covers.of_forall fun x hx => ?_
  rcases Row.mem_close.1 hx with ⟨E, hE', rfl⟩ | ⟨v, hv, hx⟩ | ⟨E, hE', rfl⟩ | ⟨p, hp, rfl⟩
  · refine Has.of_mem_eqv (Row.mem_close.2 (.inl ⟨E.substRows s, ?_, rfl⟩)) (hE E hE').symm
    rw [Row.substRows_eq, hE']
    rfl
  · rcases RowSubst.mem_compose.1 hx with ⟨hl, hx⟩ | ⟨σ, hl, hx⟩
    · exact Has.of_mem (Row.mem_close.2 (.inr (.inl ⟨v, Row.mem_vars_substRows.2
        ⟨v, hv, by simp [hl]⟩, hx⟩)))
    · rcases Row.mem_close.1 hx with ⟨G, hG, rfl⟩ | ⟨w, hw, hx⟩ | ⟨E, hE, rfl⟩ | ⟨p, hp, rfl⟩
      · have hGl : G ∈ ρ.labels s := by
          simp only [Row.labels, List.mem_append, List.mem_filterMap]
          exact .inr ⟨v, hv, by simp [hl, hG]⟩
        obtain ⟨F, hF⟩ := Row.raise_substRows_isSome hGl
        obtain rfl := hkeep.1 F (Row.raise_substRows_mem hF) G hGl
        exact Has.of_mem (Row.mem_close.2 (.inl ⟨F, hF, rfl⟩))
      · exact Has.of_mem (Row.mem_close.2 (.inr (.inl ⟨w, Row.mem_vars_substRows.2
          ⟨v, hv, by simp [hl, hw]⟩, hx⟩)))
      · exact Has.of_mem (Row.mem_close.2 (.inr (.inr (.inl ⟨E, Row.mem_effects_substRows.2
          (.inr ⟨v, hv, by simp [hl, hE]⟩), rfl⟩))))
      · exact absurd hp (by simp [hkeep.2 v hv σ hl])
  · exact Has.of_mem (Row.mem_close.2 (.inr (.inr (.inl ⟨E, Row.mem_effects_substRows.2
      (.inl hE'), rfl⟩))))
  · exact Has.of_mem (Row.mem_close.2 (.inr (.inr (.inr ⟨p, by rw [Row.resume_substRows]; exact hp,
      rfl⟩))))

mutual

/-- Instantiating a type, then reading it, is reading it under the composed
environment, when the use leaves each of its rows one `raise` label. -/
theorem Ty.close_substRows (s : RowSubst) (η : REnv) :
    ∀ τ : Ty, τ.InstantiableBy s → ((τ.substRows s).close η).Eqv (τ.close (s.compose η))
  | .int k, _ => .int k
  | .float k, _ => .float k
  | .bool, _ => .bool
  | .str, _ => .str
  | .unit, _ => .unit
  | .never, _ => .never
  | .record R, _ => .record R
  | .variant T, _ => .variant T
  | .param T, _ => .param T
  | .list τ, h => .list (Ty.close_substRows s η τ h)
  | .tuple τs, h => .tuple (closeTys_substRows s η τs fun σ hσ => h σ (by simpa [Ty.rows] using hσ))
  | .map κ τ, h => .map (Ty.close_substRows s η κ fun σ hσ => h σ (by simp [Ty.rows, hσ]))
      (Ty.close_substRows s η τ fun σ hσ => h σ (by simp [Ty.rows, hσ]))
  | .set τ, h => .set (Ty.close_substRows s η τ h)
  | .view τ, h => Ty.close_substRows s η τ h
  | .shared τ, h => .shared (Ty.close_substRows s η τ h)
  | .fn ps r ρ, h => by
    have hps : ∀ σ ∈ paramRows ps, σ.KeepsOneRaise s := fun σ hσ => h σ (by simp [Ty.rows, hσ])
    have hr : r.InstantiableBy s := fun σ hσ => h σ (by simp [Ty.rows, hσ])
    have hρ : ∀ σ ∈ ρ.rows, σ.KeepsOneRaise s := fun σ hσ => h σ (by simp [Ty.rows, hσ])
    have ⟨hc, hc'⟩ := Row.close_substRows s η ρ hρ
    exact .fn (closeParams_substRows s η ps hps) (Ty.close_substRows s η r hr) hc hc'

theorem closeTys_substRows (s : RowSubst) (η : REnv) :
    ∀ τs : List Ty, (∀ σ ∈ tysRows τs, σ.KeepsOneRaise s) →
      STysEqv (closeTys η (substTysRows s τs)) (closeTys (s.compose η) τs)
  | [], _ => .nil
  | τ :: τs, h =>
    .cons (Ty.close_substRows s η τ fun σ hσ => h σ (by simp [tysRows, hσ]))
      (closeTys_substRows s η τs fun σ hσ => h σ (by simp [tysRows, hσ]))

theorem closeParams_substRows (s : RowSubst) (η : REnv) :
    ∀ ps : List (Mode × Ty), (∀ σ ∈ paramRows ps, σ.KeepsOneRaise s) →
      SParamsEqv (closeParams η (substParamRows s ps)) (closeParams (s.compose η) ps)
  | [], _ => .nil
  | (_, τ) :: ps, h =>
    .cons (Ty.close_substRows s η τ fun σ hσ => h σ (by simp [paramRows, hσ]))
      (closeParams_substRows s η ps fun σ hσ => h σ (by simp [paramRows, hσ]))

theorem Row.close_substRows (s : RowSubst) (η : REnv) :
    ∀ ρ : Row, (∀ σ ∈ ρ.rows, σ.KeepsOneRaise s) →
      Covers ((ρ.substRows s).close η) (ρ.close (s.compose η)) ∧
        Covers (ρ.close (s.compose η)) ((ρ.substRows s).close η)
  | ⟨io, some E, vs, es, r⟩, h => by
    have hE : ∀ E', (Row.mk io (some E) vs es r).raise = some E' →
        ((E'.substRows s).close η).Eqv (E'.close (s.compose η)) := by
      rintro E' hE'
      obtain rfl := Option.some.inj hE'
      exact Ty.close_substRows s η E fun σ hσ => h σ (by simp [Row.rows, hσ])
    exact ⟨Row.close_substRows_le hE, Row.close_substRows_ge (h _ (by simp [Row.rows])) hE⟩
  | ⟨io, none, vs, es, r⟩, h => by
    have hE : ∀ E', (Row.mk io none vs es r).raise = some E' →
        ((E'.substRows s).close η).Eqv (E'.close (s.compose η)) := fun _ h => nomatch h
    exact ⟨Row.close_substRows_le hE, Row.close_substRows_ge (h _ (by simp [Row.rows])) hE⟩

end

end Stilt
