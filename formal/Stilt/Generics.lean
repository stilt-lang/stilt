import Stilt.Rows

/-!
# Type parameters

The instantiation of a function's type parameters at a use, and what typing
and its soundness need of it (declarations.function-declarations, types.no-type-arguments
and polymorphism.instantiation). A use gives each type parameter a type that
is closed and names no type parameter (`Ty.Ground`), and no row holds a type
parameter, so an instantiation replaces the type parameters outside rows and
never meets a row.
-/

namespace Stilt

/-- An instantiation of type parameters, as a use of a generic function gives
it (types.no-type-arguments). -/
abbrev TySubst := List (Name × Ty)

mutual

/-- Replaces the type parameters of a type by their instantiation. -/
def Ty.substTys (s : TySubst) : Ty → Ty
  | .param T => (s.lookup T).getD (.param T)
  | .list τ => .list (τ.substTys s)
  | .tuple τs => .tuple (substTyList s τs)
  | .map κ τ => .map (κ.substTys s) (τ.substTys s)
  | .set τ => .set (τ.substTys s)
  | .view τ => .view (τ.substTys s)
  | .shared τ => .shared (τ.substTys s)
  | .fn ps r ρ => .fn (substParamTys s ps) (r.substTys s) ρ
  | τ => τ

/-- Replaces the type parameters of a list of types. -/
def substTyList (s : TySubst) : List Ty → List Ty
  | [] => []
  | τ :: τs => τ.substTys s :: substTyList s τs

/-- Replaces the type parameters of a list of parameter types. -/
def substParamTys (s : TySubst) : List (Mode × Ty) → List (Mode × Ty)
  | [] => []
  | (m, τ) :: ps => (m, τ.substTys s) :: substParamTys s ps

end

/-- A type that names no type parameter, outside its rows or in one. -/
def Ty.Concrete (τ : Ty) : Prop := τ.params = [] ∧ ∀ ρ ∈ τ.rows, ρ.ParamFree

/-- A type that a use may give a type parameter: closed, and naming no type
parameter. -/
def Ty.Ground (τ : Ty) : Prop := τ.Closed ∧ τ.Concrete

/-- `Ty.Concrete` as a Boolean check, which `decide` evaluates. -/
def Ty.concreteCheck (τ : Ty) : Bool :=
  τ.params.isEmpty && τ.rows.all fun ρ => ρ.raise.all (·.params.isEmpty)

theorem Ty.concrete_of_check {τ : Ty} (h : τ.concreteCheck = true) : τ.Concrete := by
  simp only [Ty.concreteCheck, Bool.and_eq_true, List.isEmpty_iff, List.all_eq_true] at h
  refine ⟨h.1, fun ρ hρ E hE => ?_⟩
  have := h.2 ρ hρ
  rw [hE] at this
  simpa using this

/-- An instantiation by ground types. -/
def TySubst.Ground (s : TySubst) : Prop := ∀ p ∈ s, p.2.Ground

/-- The instantiation of a function's type parameters by the type arguments of
a use (types.no-type-arguments). -/
def FnDecl.typeArgs (d : FnDecl) (τs : List Ty) : TySubst := (d.typeParams.map TypeParam.name).zip τs

/-- Replaces the type parameters of a parameter's type. -/
def Param.substTys (s : TySubst) (p : Param) : Param := { p with type := p.type.substTys s }

/-! ## Lookups -/

theorem mem_of_lookup {β : Type} : ∀ {l : List (Name × β)} {k : Name} {b : β},
    l.lookup k = some b → (k, b) ∈ l
  | [], _, _, h => nomatch h
  | (k', b') :: l, k, b, h => by
    simp only [List.lookup_cons] at h
    split at h
    · rename_i hk
      obtain rfl := Option.some.inj h
      rw [beq_iff_eq.1 hk]
      exact List.mem_cons_self
    · exact List.mem_cons_of_mem _ (mem_of_lookup h)

theorem lookup_map_snd {β γ : Type} (f : β → γ) (k : Name) :
    ∀ l : List (Name × β), (l.map (Prod.map id f)).lookup k = (l.lookup k).map f
  | [] => rfl
  | (k', b) :: l => by
    simp only [List.map_cons, Prod.map, id, List.lookup_cons]
    split <;> simp_all [lookup_map_snd f k l]

theorem List.mem_of_lookup_zip {β : Type} :
    ∀ {ks : List Name} {bs : List β} {k : Name} {b : β}, (ks.zip bs).lookup k = some b → b ∈ bs
  | [], _, _, _, h => nomatch h
  | _ :: _, [], _, _, h => nomatch h
  | k' :: ks, b' :: bs, k, b, h => by
    simp only [List.zip_cons_cons, List.lookup_cons] at h
    split at h
    · cases h; exact List.mem_cons_self
    · exact List.mem_cons_of_mem _ (List.mem_of_lookup_zip h)

theorem List.lookup_zip_isSome {β : Type} :
    ∀ {ks : List Name} {bs : List β} {k : Name}, k ∈ ks → bs.length = ks.length →
      ((ks.zip bs).lookup k).isSome
  | [], _, _, h, _ => nomatch h
  | _ :: _, [], _, _, hl => nomatch hl
  | k' :: ks, b :: bs, k, h, hl => by
    simp only [List.zip_cons_cons, List.lookup_cons]
    split
    · rfl
    · rename_i hk
      refine List.lookup_zip_isSome ((List.mem_cons.1 h).resolve_left fun h' => ?_) (by simpa using hl)
      simp [h'] at hk

theorem Row.mem_rows_self : ∀ ρ : Row, ρ ∈ ρ.rows
  | ⟨_, some _, _, _, _⟩ => List.mem_cons_self
  | ⟨_, none, _, _, _⟩ => List.mem_singleton_self _

/-! ## Lists -/

theorem substTyList_eq_map (s : TySubst) :
    ∀ τs : List Ty, substTyList s τs = τs.map (Ty.substTys s)
  | [] => rfl
  | τ :: τs => by simp [substTyList, substTyList_eq_map s τs]

theorem substParamTys_eq_map (s : TySubst) :
    ∀ ps : List (Mode × Ty), substParamTys s ps = ps.map (Prod.map id (Ty.substTys s))
  | [] => rfl
  | (m, τ) :: ps => by simp [substParamTys, substParamTys_eq_map s ps]

theorem Param.sig_substTys (s : TySubst) (p : Param) :
    (p.substTys s).sig = Prod.map id (Ty.substTys s) p.sig := rfl

theorem map_sig_substTys (s : TySubst) (ps : List Param) :
    (ps.map (Param.substTys s)).map Param.sig = substParamTys s (ps.map Param.sig) := by
  simp [Param.sig_substTys, substParamTys_eq_map]

/-! ## What an instantiation leaves alone -/

mutual

/-- An instantiation that names none of a type's parameters leaves it as it is. -/
theorem Ty.substTys_eq_self (s : TySubst) :
    ∀ τ : Ty, (∀ T ∈ τ.params, s.lookup T = none) → τ.substTys s = τ
  | .int _, _ | .float _, _ | .bool, _ | .str, _ | .unit, _ | .never, _ => rfl
  | .record _, _ | .variant _, _ => rfl
  | .param T, h => by simp [Ty.substTys, h T (by simp [Ty.params])]
  | .list τ, h => by rw [Ty.substTys, Ty.substTys_eq_self s τ h]
  | .tuple τs, h => by rw [Ty.substTys, substTyList_eq_self s τs h]
  | .map κ τ, h => by
    rw [Ty.substTys, Ty.substTys_eq_self s κ fun T hT => h T (by simp [Ty.params, hT]),
      Ty.substTys_eq_self s τ fun T hT => h T (by simp [Ty.params, hT])]
  | .set τ, h => by rw [Ty.substTys, Ty.substTys_eq_self s τ h]
  | .view τ, h => by rw [Ty.substTys, Ty.substTys_eq_self s τ h]
  | .shared τ, h => by rw [Ty.substTys, Ty.substTys_eq_self s τ h]
  | .fn ps r ρ, h => by
    rw [Ty.substTys, substParamTys_eq_self s ps fun T hT => h T (by simp [Ty.params, hT]),
      Ty.substTys_eq_self s r fun T hT => h T (by simp [Ty.params, hT])]

theorem substTyList_eq_self (s : TySubst) :
    ∀ τs : List Ty, (∀ T ∈ tysParams τs, s.lookup T = none) → substTyList s τs = τs
  | [], _ => rfl
  | τ :: τs, h => by
    rw [substTyList, Ty.substTys_eq_self s τ fun T hT => h T (by simp [tysParams, hT]),
      substTyList_eq_self s τs fun T hT => h T (by simp [tysParams, hT])]

theorem substParamTys_eq_self (s : TySubst) :
    ∀ ps : List (Mode × Ty), (∀ T ∈ paramTysParams ps, s.lookup T = none) →
      substParamTys s ps = ps
  | [], _ => rfl
  | (m, τ) :: ps, h => by
    rw [substParamTys, Ty.substTys_eq_self s τ fun T hT => h T (by simp [paramTysParams, hT]),
      substParamTys_eq_self s ps fun T hT => h T (by simp [paramTysParams, hT])]

end

/-- A type that names no type parameter is its own instantiation. -/
theorem Ty.substTys_of_params {τ : Ty} (h : τ.params = []) (s : TySubst) : τ.substTys s = τ :=
  τ.substTys_eq_self s fun T hT => by rw [h] at hT; exact nomatch hT

@[simp] theorem Ty.substTys_nil (τ : Ty) : τ.substTys [] = τ :=
  τ.substTys_eq_self [] fun _ _ => rfl

@[simp] theorem Param.substTys_nil (p : Param) : p.substTys [] = p := by
  simp [Param.substTys]

theorem Head.params_type (h : Head) : h.type.params = [] := by
  cases h <;> rfl

theorem Ty.eq_of_head? {τ : Ty} {h : Head} (hh : τ.head? = some h) : τ = h.type := by
  cases τ <;> simp [Ty.head?] at hh <;> subst hh <;> rfl

/-! ## Rows and type parameters of an instance -/

mutual

theorem Ty.mem_rows_substTys (s : TySubst) {ρ : Row} :
    ∀ τ : Ty, ρ ∈ (τ.substTys s).rows → ρ ∈ τ.rows ∨ ∃ p ∈ s, ρ ∈ p.2.rows
  | .int _, h | .float _, h | .bool, h | .str, h | .unit, h | .never, h => .inl h
  | .record _, h | .variant _, h => .inl h
  | .param T, h => by
    simp only [Ty.substTys] at h
    cases hl : s.lookup T with
    | none => rw [hl] at h; exact .inl h
    | some σ => rw [hl] at h; exact .inr ⟨(T, σ), mem_of_lookup hl, h⟩
  | .list τ, h => Ty.mem_rows_substTys s τ h
  | .tuple τs, h => tysRows_substTys s τs h
  | .map κ τ, h => by
    simp only [Ty.substTys, Ty.rows, List.mem_append] at h ⊢
    rcases h with h | h
    · exact (Ty.mem_rows_substTys s κ h).imp .inl id
    · exact (Ty.mem_rows_substTys s τ h).imp .inr id
  | .set τ, h => Ty.mem_rows_substTys s τ h
  | .view τ, h => Ty.mem_rows_substTys s τ h
  | .shared τ, h => Ty.mem_rows_substTys s τ h
  | .fn ps r ρ', h => by
    simp only [Ty.substTys, Ty.rows, List.mem_append] at h ⊢
    rcases h with (h | h) | h
    · exact (paramRows_substTys s ps h).imp (fun h => .inl (.inl h)) id
    · exact (Ty.mem_rows_substTys s r h).imp (fun h => .inl (.inr h)) id
    · exact .inl (.inr h)

theorem tysRows_substTys (s : TySubst) {ρ : Row} :
    ∀ τs : List Ty, ρ ∈ tysRows (substTyList s τs) → ρ ∈ tysRows τs ∨ ∃ p ∈ s, ρ ∈ p.2.rows
  | [], h => .inl h
  | τ :: τs, h => by
    simp only [substTyList, tysRows, List.mem_append] at h ⊢
    rcases h with h | h
    · exact (Ty.mem_rows_substTys s τ h).imp .inl id
    · exact (tysRows_substTys s τs h).imp .inr id

theorem paramRows_substTys (s : TySubst) {ρ : Row} :
    ∀ ps : List (Mode × Ty), ρ ∈ paramRows (substParamTys s ps) →
      ρ ∈ paramRows ps ∨ ∃ p ∈ s, ρ ∈ p.2.rows
  | [], h => .inl h
  | (_, τ) :: ps, h => by
    simp only [substParamTys, paramRows, List.mem_append] at h ⊢
    rcases h with h | h
    · exact (Ty.mem_rows_substTys s τ h).imp .inl id
    · exact (paramRows_substTys s ps h).imp .inr id

end

mutual

/-- An instantiation that gives each of a type's parameters a type with no
type parameter leaves none. -/
theorem Ty.params_substTys (s : TySubst) :
    ∀ τ : Ty, (∀ T ∈ τ.params, ∃ σ, s.lookup T = some σ ∧ σ.params = []) →
      (τ.substTys s).params = []
  | .int _, _ | .float _, _ | .bool, _ | .str, _ | .unit, _ | .never, _ => rfl
  | .record _, _ | .variant _, _ => rfl
  | .param T, h => by
    obtain ⟨σ, hl, hσ⟩ := h T (by simp [Ty.params])
    simp [Ty.substTys, hl, hσ]
  | .list τ, h => Ty.params_substTys s τ h
  | .tuple τs, h => tysParams_substTys s τs h
  | .map κ τ, h => by
    simp only [Ty.substTys, Ty.params, List.append_eq_nil_iff]
    exact ⟨Ty.params_substTys s κ fun T hT => h T (by simp [Ty.params, hT]),
      Ty.params_substTys s τ fun T hT => h T (by simp [Ty.params, hT])⟩
  | .set τ, h => Ty.params_substTys s τ h
  | .view τ, h => Ty.params_substTys s τ h
  | .shared τ, h => Ty.params_substTys s τ h
  | .fn ps r _, h => by
    simp only [Ty.substTys, Ty.params, List.append_eq_nil_iff]
    exact ⟨paramTysParams_substTys s ps fun T hT => h T (by simp [Ty.params, hT]),
      Ty.params_substTys s r fun T hT => h T (by simp [Ty.params, hT])⟩

theorem tysParams_substTys (s : TySubst) :
    ∀ τs : List Ty, (∀ T ∈ tysParams τs, ∃ σ, s.lookup T = some σ ∧ σ.params = []) →
      tysParams (substTyList s τs) = []
  | [], _ => rfl
  | τ :: τs, h => by
    simp only [substTyList, tysParams, List.append_eq_nil_iff]
    exact ⟨Ty.params_substTys s τ fun T hT => h T (by simp [tysParams, hT]),
      tysParams_substTys s τs fun T hT => h T (by simp [tysParams, hT])⟩

theorem paramTysParams_substTys (s : TySubst) :
    ∀ ps : List (Mode × Ty), (∀ T ∈ paramTysParams ps, ∃ σ, s.lookup T = some σ ∧ σ.params = []) →
      paramTysParams (substParamTys s ps) = []
  | [], _ => rfl
  | (_, τ) :: ps, h => by
    simp only [substParamTys, paramTysParams, List.append_eq_nil_iff]
    exact ⟨Ty.params_substTys s τ fun T hT => h T (by simp [paramTysParams, hT]),
      paramTysParams_substTys s ps fun T hT => h T (by simp [paramTysParams, hT])⟩

end

/-! ## Views of an instance -/

theorem Ty.viewable_substTys {υ : Ty} (h : υ = .str ∨ ∃ U, υ = .list U) (s : TySubst) :
    υ.substTys s = .str ∨ ∃ U, υ.substTys s = .list U := by
  rcases h with rfl | ⟨U, rfl⟩
  · exact .inl rfl
  · exact .inr ⟨_, rfl⟩

mutual

/-- An instantiation by types whose views are viewable keeps a type's views viewable. -/
theorem Ty.ViewsViewable.substTys (s : TySubst) (hs : ∀ p ∈ s, p.2.ViewsViewable) :
    ∀ τ : Ty, τ.ViewsViewable → (τ.substTys s).ViewsViewable
  | .int _, h | .float _, h | .bool, h | .str, h | .unit, h | .never, h => h
  | .record _, h | .variant _, h => h
  | .param T, h => by
    simp only [Ty.substTys]
    cases hl : s.lookup T with
    | none => exact h
    | some σ => exact hs _ (mem_of_lookup hl)
  | .list τ, h => Ty.ViewsViewable.substTys s hs τ h
  | .tuple τs, h => tysViews_substTys s hs τs h
  | .map κ τ, h => by
    intro υ hυ
    simp only [Ty.substTys, Ty.views, List.mem_append] at hυ
    rcases hυ with hυ | hυ
    · exact Ty.ViewsViewable.substTys s hs κ (fun υ h' => h υ (by simp [Ty.views, h'])) υ hυ
    · exact Ty.ViewsViewable.substTys s hs τ (fun υ h' => h υ (by simp [Ty.views, h'])) υ hυ
  | .set τ, h => Ty.ViewsViewable.substTys s hs τ h
  | .view τ, h => by
    intro υ hυ
    simp only [Ty.substTys, Ty.views, List.mem_cons] at hυ
    rcases hυ with rfl | hυ
    · exact Ty.viewable_substTys (h τ (by simp [Ty.views])) s
    · exact Ty.ViewsViewable.substTys s hs τ (fun υ h' => h υ (by simp [Ty.views, h'])) υ hυ
  | .shared τ, h => Ty.ViewsViewable.substTys s hs τ h
  | .fn ps r ρ, h => by
    intro υ hυ
    simp only [Ty.substTys, Ty.views, List.mem_append] at hυ
    rcases hυ with (hυ | hυ) | hυ
    · exact paramTysViews_substTys s hs ps (fun υ h' => h υ (by simp [Ty.views, h'])) υ hυ
    · exact Ty.ViewsViewable.substTys s hs r (fun υ h' => h υ (by simp [Ty.views, h'])) υ hυ
    · exact h υ (by simp [Ty.views, hυ])

theorem tysViews_substTys (s : TySubst) (hs : ∀ p ∈ s, p.2.ViewsViewable) :
    ∀ τs : List Ty, (∀ υ ∈ tysViews τs, υ = .str ∨ ∃ U, υ = .list U) →
      ∀ υ ∈ tysViews (substTyList s τs), υ = .str ∨ ∃ U, υ = .list U
  | [], _ => fun _ h => nomatch h
  | τ :: τs, h => by
    intro υ hυ
    simp only [substTyList, tysViews, List.mem_append] at hυ
    rcases hυ with hυ | hυ
    · exact Ty.ViewsViewable.substTys s hs τ (fun υ h' => h υ (by simp [tysViews, h'])) υ hυ
    · exact tysViews_substTys s hs τs (fun υ h' => h υ (by simp [tysViews, h'])) υ hυ

theorem paramTysViews_substTys (s : TySubst) (hs : ∀ p ∈ s, p.2.ViewsViewable) :
    ∀ ps : List (Mode × Ty), (∀ υ ∈ paramTysViews ps, υ = .str ∨ ∃ U, υ = .list U) →
      ∀ υ ∈ paramTysViews (substParamTys s ps), υ = .str ∨ ∃ U, υ = .list U
  | [], _ => fun _ h => nomatch h
  | (_, τ) :: ps, h => by
    intro υ hυ
    simp only [substParamTys, paramTysViews, List.mem_append] at hυ
    rcases hυ with hυ | hυ
    · exact Ty.ViewsViewable.substTys s hs τ (fun υ h' => h υ (by simp [paramTysViews, h'])) υ hυ
    · exact paramTysViews_substTys s hs ps (fun υ h' => h υ (by simp [paramTysViews, h'])) υ hυ

end

/-! ## Instances of closed and well-formed types -/

theorem Ty.Closed.substTys {τ : Ty} (h : τ.Closed) {s : TySubst} (hs : s.Ground) :
    (τ.substTys s).Closed := by
  intro ρ hρ
  rcases τ.mem_rows_substTys s hρ with hρ | ⟨p, hp, hρ⟩
  · exact h ρ hρ
  · exact (hs p hp).1 ρ hρ

/-- A type that a body writes, instantiated with ground types for all the
type parameters in scope, is well formed in a scope with none. -/
theorem Ty.WellFormed.substTys {τ : Ty} {scope scope' : RowScope} (h : τ.WellFormed scope)
    {s : TySubst} (hs : s.Ground) (hview : ∀ p ∈ s, p.2.ViewsViewable)
    (hcov : ∀ p ∈ scope.types, (s.lookup p.name).isSome)
    (hvars : ∀ v ∈ scope.vars, v ∈ scope'.vars) : (τ.substTys s).WellFormed scope' := by
  refine ⟨fun ρ hρ v hv => ?_, fun T hT => ?_, fun ρ hρ => ?_, h.2.2.2.substTys s hview τ⟩
  · rcases τ.mem_rows_substTys s hρ with hρ | ⟨p, hp, hρ⟩
    · exact hvars v (h.1 ρ hρ v hv)
    · rw [(hs p hp).1 ρ hρ] at hv
      exact nomatch hv
  · rw [τ.params_substTys s fun T hT => ?_] at hT
    · exact nomatch hT
    obtain ⟨p, hp, rfl⟩ := List.mem_map.1 (h.2.1 T hT)
    obtain ⟨σ, hl⟩ := Option.isSome_iff_exists.1 (hcov p hp)
    exact ⟨σ, hl, (hs _ (mem_of_lookup hl)).2.1⟩
  · rcases τ.mem_rows_substTys s hρ with hρ | ⟨p, hp, hρ⟩
    · exact h.2.2.1 ρ hρ
    · exact (hs p hp).2.2 ρ hρ

/-- A closed type well formed in a scope with no type parameters is ground. -/
theorem Ty.ground_of_wellFormed {τ : Ty} {scope : RowScope} (h : τ.Closed)
    (hw : τ.WellFormed scope) (hnil : scope.types = []) : τ.Ground := by
  refine ⟨h, ?_, hw.2.2.1⟩
  cases hp : τ.params with
  | nil => rfl
  | cons T _ =>
    have := hw.2.1 T (by simp [hp])
    simp [hnil] at this

/-- A type with a head names no type parameter and is its own instance. -/
theorem Head.substTys_type (h : Head) (s : TySubst) : h.type.substTys s = h.type :=
  Ty.substTys_of_params h.params_type s

theorem Head.head?_type (h : Head) : h.type.head? = some h := by
  cases h <;> rfl

theorem Head.closed_type (h : Head) : h.type.Closed := by
  cases h <;> exact fun _ h => nomatch h

theorem Head.viewsViewable_type (h : Head) : h.type.ViewsViewable := by
  cases h <;> exact fun _ h => nomatch h

theorem Head.ground_type (h : Head) : h.type.Ground :=
  ⟨h.closed_type, h.params_type, by cases h <;> exact fun _ h => nomatch h⟩

/-- Instantiating type parameters with ground types adds only rows without
variables, which keep their one `raise` label under any instantiation of row
variables. -/
theorem Ty.InstantiableBy.substTys {τ : Ty} {θ : RowSubst} (h : τ.InstantiableBy θ)
    {s : TySubst} (hs : s.Ground) : (τ.substTys s).InstantiableBy θ := by
  intro ρ hρ
  rcases τ.mem_rows_substTys s hρ with hρ | ⟨p, hp, hρ⟩
  · exact h ρ hρ
  · have hv := (hs p hp).1 ρ hρ
    refine ⟨fun E hE F hF => ?_, fun v hv' => by rw [hv] at hv'; exact nomatch hv'⟩
    obtain ⟨io, raise, vars⟩ := ρ
    simp only at hv
    subst hv
    cases raise <;> simp_all [Row.labels]

/-! ## Instances fit as their types do -/

theorem Fits.substTys {a b : Ty} (h : Fits a b) (s : TySubst) : Fits (a.substTys s) (b.substTys s) := by
  cases h with
  | refl => exact .refl _
  | never => exact .never _
  | fn h => exact .fn h

end Stilt
