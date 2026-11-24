import Stilt.Optimality.Layout

/-!
# Field paths

Places that follow fields only, typed once for typing and once for values.
`FieldPath D τ fs τ'` says that following the fields `fs` from a value of type
`τ` reaches a value of type `τ'`. It gives a place's type (`PathFits`), an
expression's type (`HasType` of `Expr.project`), and, on a value of type `τ`,
a read that succeeds and a write that succeeds and keeps the type
(`ValueHasType`).

The last section types the witness's record types of
`Stilt.Optimality.Layout` with these relations.
-/

namespace Stilt

/-- Following the fields `fs` from a value of type `τ` reaches a value of type
`τ'`: each step is a field of a record type (types.field-access). -/
inductive FieldPath (D : Decls) : Ty → List Name → Ty → Prop
  | nil {τ : Ty} : FieldPath D τ [] τ
  | cons {R : Name} {r : RecordDecl} {f : Name} {σ : Ty} {fs : List Name} {τ : Ty} :
      D.record? R = some r → r.fields.lookup f = some σ → FieldPath D σ fs τ →
      FieldPath D (.record R) (f :: fs) τ

/-- `e.f₁.f₂…`: the expression that reads the fields `fs` of `e` in turn
(types.field-access). -/
def Expr.project (e : Expr) (fs : List Name) : Expr := fs.foldl .field e

namespace FieldPath

variable {D : Decls}

theorem append {τ σ ρ : Ty} {fs gs : List Name} (h : FieldPath D τ fs σ)
    (h' : FieldPath D σ gs ρ) : FieldPath D τ (fs ++ gs) ρ := by
  induction h with
  | nil => exact h'
  | cons hR hf _ ih => exact .cons hR hf (ih h')

/-- A field path types the place that follows it (expressions.places). -/
theorem pathFits {scope : RowScope} {Γ : Ctx} {fx : Effects} {τ τ' : Ty} {fs : List Name}
    (h : FieldPath D τ fs τ') : PathFits D scope Γ fx τ (fs.map .field) τ' := by
  induction h with
  | nil => exact .nil
  | cons hR hf _ ih => exact .field hR hf ih

/-- A field path types the expression that reads its fields (types.field-access). -/
theorem hasType {scope : RowScope} {Γ : Ctx} {fx : Effects} {τ τ' : Ty} {fs : List Name}
    (h : FieldPath D τ fs τ') :
    ∀ {e : Expr}, HasType D scope Γ fx e τ → HasType D scope Γ fx (e.project fs) τ' := by
  induction h with
  | nil => exact fun he => he
  | cons hR hf _ ih => exact fun he => ih (.field he hR hf)

end FieldPath

/-! ## Values along field paths -/

theorem Fits.record_inv {σ : Ty} {R : Name} (h : Fits σ (.record R)) :
    σ = .record R ∨ σ = .never := by
  cases h with
  | refl => exact .inl rfl
  | never => exact .inr rfl

/-- What a value of a record type is: a record of that type, whose fields
have the types its declaration gives them (declarations.records). -/
theorem ValueHasType.record_inv {D : Decls} {w : Value} {R : Name}
    (h : ValueHasType D w (.record R)) :
    ∃ r fields, w = .record R fields ∧ D.record? R = some r ∧
      FieldValuesHaveTypes D fields r.fields := by
  cases h with
  | record hR hfs => exact ⟨_, _, rfl, hR, hfs⟩
  | closure hfit => rcases Fits.record_inv hfit with h | h <;> cases h
  | function _ _ _ _ hfit =>
    rcases Fits.record_inv hfit with h | h <;> simp [FnDecl.type, Ty.substRows, Ty.substTys] at h

namespace FieldValuesHaveTypes

variable {D : Decls}

theorem lookup {f : Name} {σ : Ty} :
    ∀ {fields : List (Name × Value)} {declared : List (Name × Ty)},
      FieldValuesHaveTypes D fields declared → declared.lookup f = some σ →
      ∃ u, fields.lookup f = some u ∧ ValueHasType D u σ
  | [], _, h, hl => by
    cases h
    simp at hl
  | (g, w) :: _, _, h, hl => by
    cases h with
    | cons hw hrest =>
      by_cases hf : f = g
      · subst hf
        simp only [List.lookup_cons_self, Option.some.injEq] at hl ⊢
        subst hl
        exact ⟨w, rfl, hw⟩
      · rw [lookup_cons_ne hf] at hl ⊢
        exact lookup hrest hl

theorem assocSet {f : Name} {σ : Ty} {u : Value} (hu : ValueHasType D u σ) :
    ∀ {fields : List (Name × Value)} {declared : List (Name × Ty)},
      FieldValuesHaveTypes D fields declared → declared.lookup f = some σ →
      FieldValuesHaveTypes D (Stilt.assocSet fields f u) declared
  | [], _, h, _ => by
    cases h
    exact .nil
  | (g, _) :: _, _, h, hl => by
    cases h with
    | cons hw hrest =>
      by_cases hf : f = g
      · subst hf
        simp only [List.lookup_cons_self, Option.some.injEq] at hl
        subst hl
        simpa [Stilt.assocSet] using FieldValuesHaveTypes.cons hu hrest
      · rw [lookup_cons_ne hf] at hl
        simpa [Stilt.assocSet, hf] using FieldValuesHaveTypes.cons hw (assocSet hu hrest hl)

end FieldValuesHaveTypes

namespace FieldPath

variable {D : Decls}

/-- Reading along a field path from a value of its type succeeds, with a value
of the type it reaches. -/
theorem get {τ τ' : Ty} {fs : List Name} (h : FieldPath D τ fs τ') :
    ∀ {w : Value}, ValueHasType D w τ →
      ∃ u, w.get (fs.map Step.field) = .ok u ∧ ValueHasType D u τ' := by
  induction h with
  | nil => exact fun hw => ⟨_, rfl, hw⟩
  | cons hR hf _ ih =>
    intro w hw
    obtain ⟨r, fields, rfl, hR', hfs⟩ := hw.record_inv
    rw [hR] at hR'
    cases hR'
    obtain ⟨u₀, hu₀, hty⟩ := hfs.lookup hf
    obtain ⟨u, hu, hty'⟩ := ih hty
    exact ⟨u, by simp [Value.get, hu₀, hu], hty'⟩

/-- Writing a value of the type a field path reaches, along it, into a value of
its type succeeds, and keeps the type (values.let-and-var). -/
theorem set {τ τ' : Ty} {fs : List Name} (h : FieldPath D τ fs τ') {u : Value}
    (hu : ValueHasType D u τ') :
    ∀ {w : Value}, ValueHasType D w τ →
      ∃ w', w.set (fs.map Step.field) u = .ok w' ∧ ValueHasType D w' τ := by
  induction h with
  | nil => exact fun _ => ⟨u, rfl, hu⟩
  | cons hR hf _ ih =>
    intro w hw
    obtain ⟨r, fields, rfl, hR', hfs⟩ := hw.record_inv
    rw [hR] at hR'
    cases hR'
    obtain ⟨u₀, hu₀, hty⟩ := hfs.lookup hf
    obtain ⟨u', hu', hty'⟩ := ih hu hty
    refine ⟨_, ?_, .record hR (hfs.assocSet hty' hf)⟩
    simp [Value.set, hu₀, hu', Functor.map, Except.map]

end FieldPath

/-! ## The witness's record types -/

namespace Optimality

variable {D : Decls} {F : List Name} {v : Name} {K : Nat}

theorem record?_recName (hD : D.records = recDecls F v K) {b : Nat} (hb : b ≤ K) :
    D.record? (recName b) = some (recDecl F v b) := by
  simp only [Decls.record?, hD]
  exact find_recDecls hb

/-- Following names of `F` from the type with budget `b` reaches the type with
the budget less their number. -/
theorem fieldPath_recTy (hD : D.records = recDecls F v K) (hv : v ∉ F) :
    ∀ {fs : List Name} {b : Nat}, (∀ f ∈ fs, f ∈ F) → fs.length ≤ b → b ≤ K →
      FieldPath D (recTy b) fs (recTy (b - fs.length))
  | [], b, _, _, _ => by simpa using FieldPath.nil
  | f :: fs, b, hfs, hlen, hb => by
    obtain ⟨b, rfl⟩ : ∃ b', b = b' + 1 := ⟨b - 1, by simp at hlen; omega⟩
    have := fieldPath_recTy hD hv (fs := fs) (b := b)
      (fun g hg => hfs g (List.mem_cons_of_mem _ hg)) (by simp at hlen; omega) (by omega)
    refine .cons (record?_recName hD hb) ?_ (by simpa using this)
    exact lookup_recFields_field hv (hfs f List.mem_cons_self) b

/-- Every record type of the witness has the field `v`, an `i64`. -/
theorem fieldPath_leaf (hD : D.records = recDecls F v K) {b : Nat} (hb : b ≤ K) :
    FieldPath D (recTy b) [v] .i64 :=
  .cons (record?_recName hD hb) (lookup_recFields_leaf b) .nil

theorem fieldValues_const {w : Value} {τ : Ty} (hw : ValueHasType D w τ) :
    ∀ G : List Name, FieldValuesHaveTypes D (G.map fun f => (f, w)) (G.map fun f => (f, τ))
  | [] => .nil
  | _ :: G => .cons hw (fieldValues_const hw G)

/-- A literal's value has the type of its budget. -/
theorem litv_hasType (hD : D.records = recDecls F v K) :
    ∀ {b : Nat}, b ≤ K → ValueHasType D (litv F v b) (recTy b)
  | 0, hb => .record (record?_recName hD hb) (.cons (.int (by decide)) .nil)
  | b + 1, hb =>
    .record (record?_recName hD hb)
      (.cons (.int (by decide)) (fieldValues_const (litv_hasType hD (by omega)) F))

end Optimality

end Stilt
