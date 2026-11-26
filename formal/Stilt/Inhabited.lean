import Stilt.Numbers
import Stilt.Generics.Commute

/-!
# Types with values

Which types have values (patterns.types-without-values): `Never` has none, a
tuple has values when all its elements do, a declared record when all its
fields' types do, a declared variant type when one of its variants' payload
types all do, and every other type has values. `Ty.Inhabited` is the
smallest set of types these rules describe, so `type Loop = | Loop(Loop)`
has no values, as `Never` has none. `Stilt.Soundness.Inhabited` proves that
every typed value's type is inhabited, so a type that isn't has no value a
`match` must cover.

`Decls.uninhabited` decides it: it computes the declared types with values by
rounds from none, then checks that the set it reached is closed under the
rules, and says that a type has no values only when the type is outside
that set. The check makes the decision sound whatever the number of rounds.
-/

namespace Stilt

variable (D : Decls)

/-- The type `τ` has values (patterns.types-without-values). -/
inductive Ty.Inhabited : Ty → Prop
  | int (k : IntTy) : Ty.Inhabited (.int k)
  | float (k : FloatTy) : Ty.Inhabited (.float k)
  | bool : Ty.Inhabited .bool
  | str : Ty.Inhabited .str
  | unit : Ty.Inhabited .unit
  | list (τ : Ty) : Ty.Inhabited (.list τ)
  | map (κ τ : Ty) : Ty.Inhabited (.map κ τ)
  | set (τ : Ty) : Ty.Inhabited (.set τ)
  /-- A view of nothing, `View.of(x, 0, 0)`, is a view. -/
  | view (τ : Ty) : Ty.Inhabited (.view τ)
  /-- A handle is a value of `Shared<T>` whatever `T` is. -/
  | shared (τ : Ty) : Ty.Inhabited (.shared τ)
  | param (p : Name) : Ty.Inhabited (.param p)
  | fn (ps : List (Mode × Ty)) (r : Ty) (ρ : Row) : Ty.Inhabited (.fn ps r ρ)
  | tuple {τs : List Ty} : (∀ τ ∈ τs, Ty.Inhabited τ) → Ty.Inhabited (.tuple τs)
  /-- A record type at type arguments, one for each of its parameters, when its fields
  have values at them. -/
  | record {R : Name} {args : List Ty} {r : RecordDecl} :
      D.record? R = some r → args.length = r.typeParams.length →
      (∀ f ∈ r.fieldsAt args, Ty.Inhabited f.2) → Ty.Inhabited (.record R args)
  | variant {T : Name} {args : List Ty} {t : VariantDecl} {c : Name × List Ty} :
      D.variant? T = some t → args.length = t.typeParams.length → c ∈ t.ctorsAt args →
      (∀ τ ∈ c.2, Ty.Inhabited τ) → Ty.Inhabited (.variant T args)

variable {D}

/-- A type that has values once its type parameters are replaced has them before:
a parameter always has values, and a declared type's fields and payloads at the
arguments' instances are their types at the arguments, instantiated. -/
theorem Ty.Inhabited.of_substTys (hD : D.ParamsDeclared) (s : TySubst) {σ : Ty}
    (h : Ty.Inhabited D σ) : ∀ τ : Ty, τ.substTys s = σ → Ty.Inhabited D τ := by
  induction h with
  | tuple _ ih =>
    intro τ hτ
    cases τ <;> simp only [Ty.substTys, reduceCtorEq] at hτ
    case param => exact .param _
    case tuple τs =>
      rw [Ty.tuple.injEq, substTyList_eq_map] at hτ
      subst hτ
      exact .tuple fun τ' hτ' => ih _ (List.mem_map_of_mem hτ') τ' rfl
  | @record R args r hR hlen _ ih =>
    intro τ hτ
    cases τ <;> simp only [Ty.substTys, reduceCtorEq] at hτ
    case param => exact .param _
    case record R' args' =>
      obtain ⟨rfl, hargs⟩ := Ty.record.inj hτ
      rw [substTyList_eq_map] at hargs
      subst hargs
      rw [List.length_map] at hlen
      refine .record hR hlen fun f hf => ?_
      have hf' : Prod.map id (Ty.substTys s) f ∈ r.fieldsAt (args'.map (Ty.substTys s)) := by
        rw [← RecordDecl.fieldsAt_substTys (hD.fields r (List.mem_of_find?_eq_some hR)) hlen]
        exact List.mem_map_of_mem hf
      exact ih _ hf' f.2 rfl
  | @variant T args t c hT hlen hc _ ih =>
    intro τ hτ
    cases τ <;> simp only [Ty.substTys, reduceCtorEq] at hτ
    case param => exact .param _
    case variant T' args' =>
      obtain ⟨rfl, hargs⟩ := Ty.variant.inj hτ
      rw [substTyList_eq_map] at hargs
      subst hargs
      rw [List.length_map] at hlen
      rw [← VariantDecl.ctorsAt_substTys (hD.payloads t (List.mem_of_find?_eq_some hT)) hlen] at hc
      obtain ⟨c', hc', rfl⟩ := List.mem_map.1 hc
      exact .variant hT hlen hc' fun τ' hτ' => ih _ (List.mem_map_of_mem hτ') τ' rfl
  | _ =>
    intro τ hτ
    cases τ <;> simp only [Ty.substTys, reduceCtorEq] at hτ <;> constructor

/-! ## Deciding it -/

/-- Whether `τ` has values when the declared types named in `known` do and no
other declared type does. -/
def Ty.hasValues (known : List Name) : Ty → Bool
  | .never => false
  | .tuple τs => tysHaveValues known τs
  | .record R _ | .variant R _ => known.contains R
  | _ => true
where
  tysHaveValues (known : List Name) : List Ty → Bool
    | [] => true
    | τ :: τs => Ty.hasValues known τ && tysHaveValues known τs

/-- The declared types that one more round of the rules finds with values,
from those of `known`. -/
def Decls.inhabitedStep (D : Decls) (known : List Name) : List Name :=
  (D.records.filter fun r => r.fields.all fun f => f.2.hasValues known).map (·.name) ++
  (D.variants.filter fun t => t.ctors.any fun c => c.2.all (Ty.hasValues known)).map (·.name)

/-- The declared types with values that `n` rounds find, from none. -/
def Decls.inhabitedAfter (D : Decls) : Nat → List Name
  | 0 => []
  | n + 1 => D.inhabitedStep (D.inhabitedAfter n)

/-- Whether `τ` has no values: it doesn't by the declared types that as many
rounds as there are declarations find, and those are all the declared types
with values, since one more round finds no other (patterns.types-without-values). -/
def Decls.uninhabited (D : Decls) (τ : Ty) : Bool :=
  let known := D.inhabitedAfter (D.records.length + D.variants.length + 1)
  (D.inhabitedStep known).all known.contains && !τ.hasValues known

mutual

/-- A type has values by `known` when an instance of it does: a type parameter has
them, and a declared type's are its name's. -/
theorem Ty.hasValues_of_substTys (known : List Name) (s : TySubst) :
    ∀ τ : Ty, (τ.substTys s).hasValues known = true → τ.hasValues known = true
  | .tuple τs, h => by
    simp only [Ty.substTys, Ty.hasValues] at h ⊢
    exact tysHaveValues_of_substTys known s τs h
  | .never, h => h
  | .record _ _, h | .variant _ _, h => h
  | .int _, _ | .float _, _ | .bool, _ | .str, _ | .unit, _ | .list _, _ | .map _ _, _
  | .set _, _ | .view _, _ | .shared _, _ | .param _, _ | .fn _ _ _, _ => rfl

theorem tysHaveValues_of_substTys (known : List Name) (s : TySubst) :
    ∀ τs : List Ty, Ty.hasValues.tysHaveValues known (substTyList s τs) = true →
      Ty.hasValues.tysHaveValues known τs = true
  | [], _ => rfl
  | τ :: τs, h => by
    simp only [substTyList, Ty.hasValues.tysHaveValues, Bool.and_eq_true] at h ⊢
    exact ⟨Ty.hasValues_of_substTys known s τ h.1, tysHaveValues_of_substTys known s τs h.2⟩

end

/-- With the declared types of `known` closed under the rules, every type with
values has them by `known`. -/
theorem Ty.Inhabited.hasValues {known : List Name}
    (closed : ∀ R ∈ D.inhabitedStep known, R ∈ known) {τ : Ty} (h : Ty.Inhabited D τ) :
    τ.hasValues known = true := by
  have tys : ∀ τs : List Ty, (∀ τ ∈ τs, τ.hasValues known = true) →
      Ty.hasValues.tysHaveValues known τs = true := by
    intro τs
    induction τs with
    | nil => intro; rfl
    | cons τ τs ih =>
      intro hτs
      simp only [Ty.hasValues.tysHaveValues, Bool.and_eq_true]
      exact ⟨hτs τ List.mem_cons_self, ih fun σ hσ => hτs σ (List.mem_cons_of_mem _ hσ)⟩
  induction h with
  | tuple _ ih => exact tys _ ih
  | @record R args r hR _ _ ih =>
    have hname : r.name = R := by
      have := List.find?_some hR
      simpa using this
    simp only [Ty.hasValues, List.contains_iff_mem]
    refine closed R ?_
    unfold Decls.inhabitedStep
    refine List.mem_append_left _ (List.mem_map.2 ⟨r, List.mem_filter.2 ⟨?_, ?_⟩, hname⟩)
    · exact List.mem_of_find?_eq_some hR
    · refine List.all_eq_true.2 fun f hf => Ty.hasValues_of_substTys known (r.typeArgs args) f.2 ?_
      exact ih (Prod.map id (Ty.substTys (r.typeArgs args)) f) (List.mem_map_of_mem hf)
  | @variant T args t c hT _ hc _ ih =>
    have hname : t.name = T := by
      have := List.find?_some hT
      simpa using this
    simp only [Ty.hasValues, List.contains_iff_mem]
    refine closed T ?_
    unfold Decls.inhabitedStep
    refine List.mem_append_right _ (List.mem_map.2 ⟨t, List.mem_filter.2 ⟨?_, ?_⟩, hname⟩)
    · exact List.mem_of_find?_eq_some hT
    · obtain ⟨c', hc', rfl⟩ := List.mem_map.1 hc
      refine List.any_eq_true.2 ⟨c', hc', List.all_eq_true.2 fun τ hτ => ?_⟩
      exact Ty.hasValues_of_substTys known _ τ (ih _ (List.mem_map_of_mem hτ))
  | _ => rfl

/-- A type that `uninhabited` finds without values has none (patterns.types-without-values). -/
theorem Decls.uninhabited_sound {τ : Ty} (h : D.uninhabited τ = true) : ¬ Ty.Inhabited D τ := by
  intro hτ
  simp only [Decls.uninhabited, Bool.and_eq_true, List.all_eq_true, List.contains_iff_mem,
    Bool.not_eq_true'] at h
  rw [hτ.hasValues h.1] at h
  exact Bool.noConfusion h.2

end Stilt
