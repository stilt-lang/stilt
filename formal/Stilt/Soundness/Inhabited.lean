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

/-- The type of a typed value is inhabited, whatever type closes to it: by induction over
the typing, whose records, variants and tuples are inhabited by their parts' values. -/
theorem Value.Typed.inhabited {v : Value} {σ : STy} (hv : Value.Typed D v σ) :
    ∀ (τ : Ty) (η : REnv), τ.close η = σ → Ty.Inhabited D τ := by
  refine Value.Typed.rec
    (motive_1 := fun _ σ _ => ∀ (τ : Ty) (η : REnv), τ.close η = σ → Ty.Inhabited D τ)
    (motive_2 := fun _ σs _ => ∀ σ ∈ σs, ∀ (τ : Ty) (η : REnv), τ.close η = σ → Ty.Inhabited D τ)
    (motive_3 := fun _ _ _ _ => True)
    (motive_4 := fun _ declared _ => ∀ f ∈ declared, Ty.Inhabited D f.2)
    (motive_5 := fun _ τs _ => ∀ τ ∈ τs, Ty.Inhabited D τ)
    ?int ?float ?str ?bool ?unit ?record ?variant ?list ?tuple ?map ?set ?closure ?function ?handle
    ?enil ?econs ?fnil ?fcons ?dnil ?dcons ?vnil ?vcons hv
  case int | float | str | bool | unit =>
    intros; rename_i τ _ h; cases τ <;> (try exact .view _) <;> simp [Ty.close] at h <;> subst_vars <;> constructor
  case list | map | set =>
    intros; rename_i τ _ h; cases τ <;> (try exact .view _) <;> simp [Ty.close] at h <;> constructor
  case record =>
    intro R r fields hR _ ih τ η h
    cases τ <;> (try exact .view _) <;> simp [Ty.close] at h
    subst h
    exact .record hR ih
  case variant =>
    intro T t C τs payload hT hC _ ih τ η h
    cases τ <;> (try exact .view _) <;> simp [Ty.close] at h
    subst h
    exact .variant (c := (C, τs)) hT (mem_of_lookup hC) ih
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
  case dnil => intro _ h; exact nomatch h
  case dcons =>
    intro f v ty fields declared _ _ ihv ihs g hg
    rcases List.mem_cons.1 hg with rfl | hg
    · exact ihv _ _ rfl
    · exact ihs g hg
  case vnil => intro _ h; exact nomatch h
  case vcons =>
    intro v ty vs τs _ _ ihv ihs τ' hτ'
    rcases List.mem_cons.1 hτ' with rfl | hτ'
    · exact ihv _ _ rfl
    · exact ihs τ' hτ'

end Stilt
