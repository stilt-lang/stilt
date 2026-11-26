import Stilt.Soundness.Values

/-!
# Typed values have inhabited types

Every value of a type has a type with values (patterns.types-without-values):
a record's fields, a variant's payload and a tuple's elements are values of
their types, which are therefore inhabited, and so is the type that holds
them. So a type that `Ty.Inhabited` doesn't hold has no value, and a `match`
needs no arm for it.
-/

namespace Stilt

variable {D : Decls}

theorem closeTys_eq_map' (η : REnv) : ∀ τs : List Ty, closeTys η τs = τs.map (Ty.close η)
  | [] => rfl
  | τ :: τs => by simp [closeTys, closeTys_eq_map' η τs]

/-- A closed type has the shape of the type it closes, or is a view of one: closing
changes rows only, and reads a view as the part it reads. -/
theorem Ty.close_tuple_inv {η : REnv} {τ : Ty} {σs : List STy} (h : τ.close η = .tuple σs) :
    (∃ τs, τ = .tuple τs ∧ σs = τs.map (Ty.close η)) ∨ ∃ τ', τ = .view τ' := by
  cases τ <;> simp [Ty.close] at h
  · exact .inl ⟨_, rfl, by rw [← h, closeTys_eq_map']⟩
  · exact .inr ⟨_, rfl⟩

/-- A type that closes to `.record R as` or to `.variant T as` is that type at arguments
that close to `as`, or a view of one. -/
theorem Ty.close_declared_inv {η : REnv} {τ : Ty} {R : Name} {as : List STy}
    (h : τ.close η = .record R as ∨ τ.close η = .variant R as) :
    (∃ τs, (τ = .record R τs ∨ τ = .variant R τs) ∧ closeTys η τs = as) ∨ ∃ τ', τ = .view τ' := by
  cases τ <;> simp [Ty.close] at h
  all_goals first
    | exact .inr ⟨_, rfl⟩
    | (obtain ⟨rfl, rfl⟩ := h; exact .inl ⟨_, by simp, rfl⟩)

/-- A declared field or payload type, at arguments that close to the run-time arguments
`π`, closes to the declared type at `π`. -/
theorem Ty.semAt_of_closed {τ : Ty} (hc : τ.Closed) (names : List Name) (τs : List Ty) (η : REnv) :
    (τ.substTys (names.zip τs)).close η = τ.semAt (names.zip (closeTys η τs)) :=
  hc.close_substTys names τs η

theorem length_closeTys (η : REnv) : ∀ τs : List Ty, (closeTys η τs).length = τs.length
  | [] => rfl
  | _ :: τs => by simp [closeTys, length_closeTys η τs]

/-- The type of a typed value is inhabited, whatever type closes to it: by induction over
the typing, whose records, variants and tuples are inhabited by their parts' values. A
field's or payload's type, which a declaration states closed, at the arguments of the
type, closes to the type its value has. -/
theorem Value.Typed.inhabited (hD : D.WellFormed) {v : Value} {σ : STy} (hv : Value.Typed D v σ) :
    ∀ (τ : Ty) (η : REnv), τ.close η = σ → Ty.Inhabited D τ := by
  refine Value.Typed.rec
    (motive_1 := fun _ σ _ => ∀ (τ : Ty) (η : REnv), τ.close η = σ → Ty.Inhabited D τ)
    (motive_2 := fun _ σs _ => ∀ σ ∈ σs, ∀ (τ : Ty) (η : REnv), τ.close η = σ → Ty.Inhabited D τ)
    (motive_3 := fun _ _ _ _ => True)
    (motive_4 := fun _ declared π _ => ∀ f ∈ declared, ∀ (τ : Ty) (η : REnv),
      τ.close η = f.2.semAt π → Ty.Inhabited D τ)
    (motive_5 := fun _ τs π _ => ∀ σ ∈ τs, ∀ (τ : Ty) (η : REnv),
      τ.close η = σ.semAt π → Ty.Inhabited D τ)
    ?int ?float ?str ?bool ?unit ?record ?variant ?list ?tuple ?map ?set ?closure ?function ?handle
    ?enil ?econs ?fnil ?fcons ?dnil ?dcons ?vnil ?vcons hv
  case int | float | str | bool | unit =>
    intros; rename_i τ _ h; cases τ <;> (try exact .view _) <;> simp [Ty.close] at h <;> subst_vars <;> constructor
  case list | map | set =>
    intros; rename_i τ _ h; cases τ <;> (try exact .view _) <;> simp [Ty.close] at h <;> constructor
  case record =>
    intro R as r fields hR hl _ ih τ η h
    obtain ⟨τs, hτ | hτ, rfl⟩ | ⟨_, rfl⟩ := Ty.close_declared_inv (.inl h)
    · subst hτ
      rw [length_closeTys] at hl
      refine .record hR hl fun f hf => ?_
      obtain ⟨g, hg, rfl⟩ := List.mem_map.1 hf
      exact ih g hg _ η (Ty.semAt_of_closed (hD.fieldsClosed r (List.mem_of_find?_eq_some hR) g hg) _ _ η)
    · subst hτ; simp [Ty.close] at h
    · exact .view _
  case variant =>
    intro T as t C τs payload hT hl hC _ ih τ η h
    obtain ⟨σs, hτ | hτ, rfl⟩ | ⟨_, rfl⟩ := Ty.close_declared_inv (.inr h)
    · subst hτ; simp [Ty.close] at h
    · subst hτ
      rw [length_closeTys] at hl
      refine .variant (c := (C, τs.map (Ty.substTys (t.typeArgs σs)))) hT hl
        (List.mem_map_of_mem (mem_of_lookup hC)) fun σ hσ => ?_
      obtain ⟨ρ, hρ, rfl⟩ := List.mem_map.1 hσ
      exact ih ρ hρ _ η (Ty.semAt_of_closed (hD.payloadsClosed t (List.mem_of_find?_eq_some hT) _
        (mem_of_lookup hC) ρ hρ) _ _ η)
    · exact .view _
  case tuple =>
    intro vs σs _ ih τ η h
    obtain ⟨τs, rfl, hσs⟩ | ⟨_, rfl⟩ := Ty.close_tuple_inv h
    · exact .tuple fun τ' hτ' => ih _ (hσs ▸ List.mem_map_of_mem hτ') τ' η rfl
    · exact .view _
  case closure =>
    intros
    rename_i hfit _ _ τ _ h
    obtain ⟨_, _, _, hσ⟩ := hfit.fn_fn rfl
    rw [hσ] at h
    cases τ <;> (try exact .view _) <;> simp [Ty.close] at h
    constructor
  case function =>
    intros
    rename_i hfit τ _ h
    obtain ⟨_, _, _, hσ⟩ := hfit.fn_fn rfl
    rw [hσ] at h
    cases τ <;> (try exact .view _) <;> simp [Ty.close] at h
    constructor
  case handle =>
    intros
    rename_i hfit τ _ h
    obtain ⟨_, hσ⟩ := hfit.shared_shared rfl
    rw [hσ] at h
    cases τ <;> (try exact .view _) <;> simp [Ty.close] at h
    constructor
  case enil => intro _ h; exact nomatch h
  case econs =>
    intro v σ vs σs _ _ ihv ihs σ' hσ' τ η h
    rcases List.mem_cons.1 hσ' with rfl | hσ'
    · exact ihv τ η h
    · exact ihs σ' hσ' τ η h
  case fnil | fcons => intros; trivial
  case dnil => intro _ _ h; exact nomatch h
  case dcons =>
    intro f v ty fields declared π _ _ ihv ihs g hg
    rcases List.mem_cons.1 hg with rfl | hg
    · exact ihv
    · exact ihs g hg
  case vnil => intro _ _ h; exact nomatch h
  case vcons =>
    intro v ty vs τs π _ _ ihv ihs τ' hτ'
    rcases List.mem_cons.1 hτ' with rfl | hτ'
    · exact ihv
    · exact ihs τ' hτ'

end Stilt
