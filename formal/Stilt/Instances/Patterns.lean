import Stilt.Instances.Context

/-!
# Patterns of instances

A pattern checked against a type that names type parameters fits the type's
instance, binding names of the instantiated types, and arms that cover a type
cover its instance. A type parameter is matched only by patterns that match
anything, which match every instance too, since a body knows nothing of it but
its bounds (polymorphism.rigid-types); the types a pattern reads from
declarations, those of record fields and variant payloads at the scrutinee's
type arguments, are at the instance those types at the arguments' instances.
-/

namespace Stilt

section

variable {D : Decls} (s : TySubst)

/-- A record type's fields at type arguments, instantiated, are its fields at the
arguments' instances. -/
theorem Decls.WellFormed.fieldsAt_substTys (hD : D.WellFormed) {R : Name} {r : RecordDecl}
    (hR : D.record? R = some r) {τs : List Ty} (hlen : τs.length = r.typeParams.length) :
    (r.fieldsAt τs).map (Prod.map id (Ty.substTys s)) = r.fieldsAt (τs.map (Ty.substTys s)) :=
  RecordDecl.fieldsAt_substTys (hD.paramsDeclared.fields r (List.mem_of_find?_eq_some hR)) hlen s

/-- A variant type's payloads at type arguments, instantiated, are its payloads at the
arguments' instances. -/
theorem Decls.WellFormed.ctorsAt_substTys (hD : D.WellFormed) {T : Name} {t : VariantDecl}
    (hT : D.variant? T = some t) {τs : List Ty} (hlen : τs.length = t.typeParams.length) :
    (t.ctorsAt τs).map (Prod.map id (List.map (Ty.substTys s))) =
      t.ctorsAt (τs.map (Ty.substTys s)) :=
  VariantDecl.ctorsAt_substTys (hD.paramsDeclared.payloads t (List.mem_of_find?_eq_some hT)) hlen s

/-- A field's type at type arguments, instantiated, is its type at the arguments' instances. -/
theorem Decls.WellFormed.lookup_fieldsAt_substTys (hD : D.WellFormed) {R : Name} {r : RecordDecl}
    (hR : D.record? R = some r) {τs : List Ty} (hlen : τs.length = r.typeParams.length)
    {f : Name} {τ : Ty} (hf : (r.fieldsAt τs).lookup f = some τ) :
    (r.fieldsAt (τs.map (Ty.substTys s))).lookup f = some (τ.substTys s) := by
  rw [← hD.fieldsAt_substTys s hR hlen, lookup_map_snd, hf]
  rfl

/-- A variant's payload types at type arguments, instantiated, are its payload types at the
arguments' instances. -/
theorem Decls.WellFormed.lookup_ctorsAt_substTys (hD : D.WellFormed) {T : Name} {t : VariantDecl}
    (hT : D.variant? T = some t) {τs : List Ty} (hlen : τs.length = t.typeParams.length)
    {C : Name} {σs : List Ty} (hC : (t.ctorsAt τs).lookup C = some σs) :
    (t.ctorsAt (τs.map (Ty.substTys s))).lookup C = some (σs.map (Ty.substTys s)) := by
  rw [← hD.ctorsAt_substTys s hT hlen, lookup_map_snd, hC]
  rfl

mutual

/-- A pattern fits the instance of the type it fits. -/
theorem PatFits.substTys (hD : D.WellFormed) :
    ∀ {p : Pattern} {τ : Ty} {σs : List Ty}, PatFits D p τ σs →
    PatFits D p (τ.substTys s) (σs.map (Ty.substTys s))
  | _, _, _, .wild => .wild
  | _, _, _, .bind => .bind
  | _, _, _, .int h => .int h
  | _, _, _, .bool => .bool
  | _, _, _, .str => .str
  | _, _, _, .unit => .unit
  | _, _, _, .tuple (τs := τs) h => by
    show PatFits D _ (.tuple (substTyList s τs)) _
    rw [substTyList_eq_map]
    exact .tuple (PatsFit.substTys hD h)
  | _, _, _, .record (args := args) hR hlen hnd h => by
    show PatFits D _ (.record _ (substTyList s args)) _
    rw [substTyList_eq_map]
    exact .record hR (by rw [List.length_map]; exact hlen) hnd
      (FieldPatsFit.substTys hD (hD.fieldsAt_substTys s hR hlen) h)
  | _, _, _, .variant (args := args) hT hlen hC h => by
    show PatFits D _ (.variant _ (substTyList s args)) _
    rw [substTyList_eq_map]
    exact .variant hT (by rw [List.length_map]; exact hlen) (hD.lookup_ctorsAt_substTys s hT hlen hC)
      (PatsFit.substTys hD h)
  | _, _, _, .or hp hq hb => .or (PatFits.substTys hD hp) (PatFits.substTys hD hq) hb
  | _, _, _, .const (c := c) hC hτ hw hv hp => by
    subst hτ
    have hc : c.type.substTys s = c.type :=
      Ty.substTys_of_params (hD.constTypes c (List.mem_of_find?_eq_some hC)) s
    have hp' := PatFits.substTys hD hp
    rw [hc] at hp' ⊢
    exact .const hC rfl hw hv hp'
  | _, _, _, .list (ps := ps) (r := r) (τ := τ) h => by
    have h' := PatsFit.substTys hD h
    rw [List.map_replicate] at h'
    rw [List.map_append, List.map_map]
    exact .list h'

theorem PatsFit.substTys (hD : D.WellFormed) :
    ∀ {ps : List Pattern} {τs σs : List Ty}, PatsFit D ps τs σs →
    PatsFit D ps (τs.map (Ty.substTys s)) (σs.map (Ty.substTys s))
  | _, _, _, .nil => .nil
  | _, _, _, .cons hp hps => by
    rw [List.map_append]
    exact .cons (PatFits.substTys hD hp) (PatsFit.substTys hD hps)

theorem FieldPatsFit.substTys (hD : D.WellFormed) :
    ∀ {declared declared' : List (Name × Ty)} {fps : List (Name × Pattern)} {σs : List Ty},
      declared.map (Prod.map id (Ty.substTys s)) = declared' → FieldPatsFit D declared fps σs →
      FieldPatsFit D declared' fps (σs.map (Ty.substTys s))
  | _, _, _, _, rfl, .nil => .nil
  | _, _, _, _, rfl, .cons (τ := τ) hl hp hfps => by
    rw [List.map_append]
    exact .cons (by rw [lookup_map_snd, hl]; rfl) (PatFits.substTys hD hp)
      (FieldPatsFit.substTys hD rfl hfps)

end

/-- Rows that cover types cover their instances. -/
theorem Exhaustive.substTys (hD : D.WellFormed) {P : Rows} {τs : List Ty}
    (h : Exhaustive D P τs) :
    Exhaustive D P (τs.map (Ty.substTys s)) := by
  induction h with
  | done h => exact .done h
  | empty hτ => exact .empty fun h => hτ (h.of_substTys hD.paramsDeclared s _ rfl)
  | default _ ih => exact .default ih
  | bool _ _ iht ihf => exact .bool iht ihf
  | unit _ ih => exact .unit ih
  | @tuple P σs τs _ ih =>
    show Exhaustive D _ (.tuple (substTyList s σs) :: _)
    rw [substTyList_eq_map]
    rw [List.map_append] at ih
    exact .tuple (by rw [List.length_map]; exact ih)
  | @record P R args r τs hR hlen _ ih =>
    show Exhaustive D _ (.record _ (substTyList s args) :: _)
    rw [substTyList_eq_map]
    refine .record hR (by rw [List.length_map]; exact hlen) ?_
    rw [List.map_append, List.map_map] at ih
    rw [← hD.fieldsAt_substTys s hR hlen, List.map_map]
    exact ih
  | @variant P T args t τs hT hlen _ ih =>
    show Exhaustive D _ (.variant _ (substTyList s args) :: _)
    rw [substTyList_eq_map]
    refine .variant hT (by rw [List.length_map]; exact hlen) fun c hc => ?_
    rw [← hD.ctorsAt_substTys s hT hlen] at hc
    obtain ⟨c', hc', rfl⟩ := List.mem_map.1 hc
    have h := ih c' hc'
    rw [List.map_append] at h
    simpa using h
  | list m _ _ ih ihl =>
    refine .list m (fun n hn => ?_) ?_
    · have h := ih n hn
      rwa [List.map_append, List.map_replicate] at h
    · rwa [List.map_append, List.map_replicate] at ihl

end

end Stilt
