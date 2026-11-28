import Stilt.Soundness.Inhabited

/-!
# Keys that equal themselves

A value of a key type equals itself as a map finds keys (`Value.keyEq`): integers,
Booleans, strings and `()` by their values, and tuples, lists, records and variants part by
part (traits.structural-impls), each part of a key type too (`Decls.Key`). A float, which
may be a NaN, and a function value are of no key type (std.map-key-bounds). So a store
`m[k] = v` of a well-typed program leaves a map that finds `k` (facts.keys).
-/

namespace Stilt

theorem Value.payloadKeyEq_self : ∀ {vs : List Value}, (∀ v ∈ vs, v.keyEq v = true) →
    Value.keyEq.payloadKeyEq vs vs = true
  | [], _ => by simp [Value.keyEq.payloadKeyEq]
  | v :: vs, h => by
    simp only [Value.keyEq.payloadKeyEq, Bool.and_eq_true]
    exact ⟨h v List.mem_cons_self, payloadKeyEq_self fun u hu => h u (List.mem_cons_of_mem _ hu)⟩

theorem Value.fieldsKeyEq_positions : ∀ (i : Nat) (vs : List Value),
    Value.keyEq.fieldsKeyEq (positionsFrom i vs) (positionsFrom i vs) =
      Value.keyEq.payloadKeyEq vs vs
  | _, [] => by simp [positionsFrom, Value.keyEq.fieldsKeyEq, Value.keyEq.payloadKeyEq]
  | i, v :: vs => by
    simp [positionsFrom, Value.keyEq.fieldsKeyEq, Value.keyEq.payloadKeyEq,
      fieldsKeyEq_positions (i + 1) vs]

section

variable {D : Decls} (hD : D.WellFormed) {S : Ty → Prop} (hS : ∀ τ, S τ → D.KeyStep S τ)
include hD hS

/-- A typed value of a type that closes from one of a set of key types equals itself. -/
theorem Value.Typed.keyEq_self {v : Value} {σ : STy} (hv : Value.Typed D v σ) :
    ∀ (τ : Ty) (η : REnv), τ.close η = σ → S τ → v.keyEq v = true := by
  refine Value.Typed.rec
    (motive_1 := fun v σ _ => ∀ (τ : Ty) (η : REnv), τ.close η = σ → S τ → v.keyEq v = true)
    (motive_2 := fun vs σs _ => (∀ σ ∈ σs, ∃ (τ : Ty) (η : REnv), τ.close η = σ ∧ S τ) →
      Value.keyEq.payloadKeyEq vs vs = true)
    (motive_3 := fun _ _ _ _ => True)
    (motive_4 := fun fields declared π _ =>
      (∀ g ∈ declared, ∃ (τ : Ty) (η : REnv), τ.close η = g.2.semAt π ∧ S τ) →
        Value.keyEq.fieldsKeyEq fields fields = true)
    (motive_5 := fun vs τs π _ => (∀ ρ ∈ τs, ∃ (τ : Ty) (η : REnv), τ.close η = ρ.semAt π ∧ S τ) →
      Value.keyEq.payloadKeyEq vs vs = true)
    ?int ?float ?str ?bool ?unit ?record ?variant ?list ?tuple ?map ?set ?closure ?function ?handle
    ?enil ?econs ?fnil ?fcons ?dnil ?dcons ?vnil ?vcons hv
  case int | str | bool | unit => intros; simp [Value.keyEq]
  case float | map | set =>
    intros; rename_i τ _ h hs
    exfalso
    cases τ <;> simp [Ty.close] at h <;> simpa [Decls.KeyStep] using hS _ hs
  case closure =>
    intros
    rename_i hfit _ _ τ _ h hs
    obtain ⟨_, _, _, hσ⟩ := hfit.fn_fn rfl
    rw [hσ] at h
    exfalso
    cases τ <;> simp [Ty.close] at h <;> simpa [Decls.KeyStep] using hS _ hs
  case function =>
    intros
    rename_i hfit τ _ h hs
    obtain ⟨_, _, _, hσ⟩ := hfit.fn_fn rfl
    rw [hσ] at h
    exfalso
    cases τ <;> simp [Ty.close] at h <;> simpa [Decls.KeyStep] using hS _ hs
  case handle =>
    intros
    rename_i hfit τ _ h hs
    obtain ⟨_, hσ⟩ := hfit.shared_shared rfl
    rw [hσ] at h
    exfalso
    cases τ <;> simp [Ty.close] at h <;> simpa [Decls.KeyStep] using hS _ hs
  case record =>
    intro R as r fields hR hl _ ih τ η h hs
    obtain ⟨τs, hτ | hτ, rfl⟩ | ⟨_, rfl⟩ := Ty.close_declared_inv (.inl h)
    · subst hτ
      obtain ⟨-, -, -, r', hR', hf⟩ := hS _ hs
      rw [hR] at hR'; cases hR'
      simp only [Value.keyEq, beq_self_eq_true, Bool.true_and]
      refine ih fun g hg => ⟨_, η, Ty.semAt_of_closed
        (hD.fieldsClosed r (List.mem_of_find?_eq_some hR) g hg) _ _ η,
        hf (g.1, g.2.substTys (r.typeArgs τs)) (List.mem_map_of_mem hg)⟩
    · subst hτ; simp [Ty.close] at h
    · exact absurd (hS _ hs) (by simp [Decls.KeyStep])
  case variant =>
    intro T as t C τs payload hT hl hC _ ih τ η h hs
    obtain ⟨σs, hτ | hτ, rfl⟩ | ⟨_, rfl⟩ := Ty.close_declared_inv (.inr h)
    · subst hτ; simp [Ty.close] at h
    · subst hτ
      obtain ⟨-, -, -, t', hT', hc⟩ := hS _ hs
      rw [hT] at hT'; cases hT'
      simp only [Value.keyEq, beq_self_eq_true, Bool.true_and]
      refine ih fun ρ hρ => ⟨_, η, Ty.semAt_of_closed (hD.payloadsClosed t
        (List.mem_of_find?_eq_some hT) _ (mem_of_lookup hC) ρ hρ) _ _ η,
        hc (C, τs.map (Ty.substTys (t.typeArgs σs))) (List.mem_map_of_mem (mem_of_lookup hC)) _
          (List.mem_map_of_mem hρ)⟩
    · exact absurd (hS _ hs) (by simp [Decls.KeyStep])
  case list =>
    intro σ vs _ ih τ η h hs
    cases τ <;> simp [Ty.close] at h
    · rename_i κ
      have hκ : S κ := by simpa [Decls.KeyStep] using hS _ hs
      simp only [Value.keyEq]
      exact Value.payloadKeyEq_self fun v hv => ih v hv κ η h hκ
    · exact absurd (hS _ hs) (by simp [Decls.KeyStep])
  case tuple =>
    intro vs σs _ ih τ η h hs
    obtain ⟨τs, rfl, hσs⟩ | ⟨_, rfl⟩ := Ty.close_tuple_inv h
    · have hκ : ∀ κ ∈ τs, S κ := by simpa [Decls.KeyStep] using hS _ hs
      simp only [Value.tuple, positions, Value.keyEq, beq_self_eq_true, Bool.true_and,
        Value.fieldsKeyEq_positions]
      refine ih fun σ hσ => ?_
      rw [hσs] at hσ
      obtain ⟨κ, hκm, rfl⟩ := List.mem_map.1 hσ
      exact ⟨κ, η, rfl, hκ κ hκm⟩
    · exact absurd (hS _ hs) (by simp [Decls.KeyStep])
  case enil => intro _; simp [Value.keyEq.payloadKeyEq]
  case econs =>
    intro v σ vs σs _ _ ihv ihs h
    obtain ⟨τ, η, hτ, hs⟩ := h σ List.mem_cons_self
    simp only [Value.keyEq.payloadKeyEq, Bool.and_eq_true]
    exact ⟨ihv τ η hτ hs, ihs fun σ' hσ' => h σ' (List.mem_cons_of_mem _ hσ')⟩
  case fnil | fcons => intros; trivial
  case dnil => intro _; simp [Value.keyEq.fieldsKeyEq]
  case dcons =>
    intro f v ty fields declared π _ _ ihv ihs h
    obtain ⟨τ, η, hτ, hs⟩ := h (f, ty) List.mem_cons_self
    simp only [Value.keyEq.fieldsKeyEq, Bool.and_eq_true]
    exact ⟨ihv τ η hτ hs, ihs fun g hg => h g (List.mem_cons_of_mem _ hg)⟩
  case vnil => intro _; simp [Value.keyEq.payloadKeyEq]
  case vcons =>
    intro v ty vs τs π _ _ ihv ihs h
    obtain ⟨τ, η, hτ, hs⟩ := h ty List.mem_cons_self
    simp only [Value.keyEq.payloadKeyEq, Bool.and_eq_true]
    exact ⟨ihv τ η hτ hs, ihs fun ρ hρ => h ρ (List.mem_cons_of_mem _ hρ)⟩

end

/-- A value of a key type of the program equals itself as a map finds keys. -/
theorem Value.Typed.keyEq_of_key {D : Decls} (hD : D.WellFormed) {v : Value} {κ : Ty} {η : REnv}
    (hv : Value.Typed D v (κ.close η)) (hκ : D.Key κ) : v.keyEq v = true := by
  obtain ⟨S, hs, hS⟩ := hκ
  exact hv.keyEq_self hD hS κ η rfl hs

end Stilt
