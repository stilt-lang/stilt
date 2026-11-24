import Stilt.Instances.Context

/-!
# Patterns of instances

A pattern checked against a type that names type parameters fits the type's
instance, binding names of the instantiated types, and arms that cover a type
cover its instance. A type parameter is matched only by patterns that match
anything, which match every instance too; the types a pattern reads from
declarations, those of record fields and variant payloads, name no type
parameter (polymorphism.rigid-types).
-/

namespace Stilt

section

variable {D : Decls} (s : TySubst)

private theorem fieldParams (hD : D.WellFormed) {R : Name} {r : RecordDecl}
    (hR : D.record? R = some r) :
    ∀ p ∈ r.fields, p.2.params = [] :=
  fun p hp => (hD.fieldsConcrete r (List.mem_of_find?_eq_some hR) p hp).1

private theorem payloadParams (hD : D.WellFormed) {T : Name} {t : VariantDecl}
    (hT : D.variant? T = some t) :
    ∀ c ∈ t.ctors, ∀ τ ∈ c.2, τ.params = [] :=
  fun c hc τ hτ => (hD.payloadsConcrete t (List.mem_of_find?_eq_some hT) c hc τ hτ).1

private theorem map_substTys_of_params : ∀ {τs : List Ty}, (∀ τ ∈ τs, τ.params = []) →
    τs.map (Ty.substTys s) = τs
  | [], _ => rfl
  | τ :: τs, h => by
    rw [List.map_cons, Ty.substTys_of_params (h τ List.mem_cons_self) s,
      map_substTys_of_params fun σ hσ => h σ (List.mem_cons_of_mem _ hσ)]

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
  | _, _, _, .record hR hnd h => .record hR hnd (FieldPatsFit.substTys hD (fieldParams hD hR) h)
  | _, _, _, .variant (τs := τs) hT hC h => by
    have h' := PatsFit.substTys hD h
    rw [map_substTys_of_params s (payloadParams hD hT _ (mem_of_lookup hC))] at h'
    exact .variant hT hC h'
  | _, _, _, .or hp hq hb => .or (PatFits.substTys hD hp) (PatFits.substTys hD hq) hb
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
    ∀ {declared : List (Name × Ty)} {fps : List (Name × Pattern)} {σs : List Ty}, (∀ p ∈ declared, p.2.params = []) → FieldPatsFit D declared fps σs →
      FieldPatsFit D declared fps (σs.map (Ty.substTys s))
  | _, _, _, _, .nil => .nil
  | _, _, _, hc, .cons (τ := τ) hl hp hfps => by
    have hp' := PatFits.substTys hD hp
    rw [Ty.substTys_of_params (hc _ (mem_of_lookup hl))] at hp'
    rw [List.map_append]
    exact .cons hl hp' (FieldPatsFit.substTys hD hc hfps)

end

/-- Rows that cover types cover their instances. -/
theorem Exhaustive.substTys (hD : D.WellFormed) {P : Rows} {τs : List Ty}
    (h : Exhaustive D P τs) :
    Exhaustive D P (τs.map (Ty.substTys s)) := by
  induction h with
  | done h => exact .done h
  | empty hτ => exact .empty fun h => hτ (h.of_substTys s)
  | default _ ih => exact .default ih
  | bool _ _ iht ihf => exact .bool iht ihf
  | unit _ ih => exact .unit ih
  | @tuple P σs τs _ ih =>
    show Exhaustive D _ (.tuple (substTyList s σs) :: _)
    rw [substTyList_eq_map]
    rw [List.map_append] at ih
    exact .tuple (by rw [List.length_map]; exact ih)
  | record hR _ ih =>
    rw [List.map_append, map_substTys_of_params s fun τ hτ => by
      obtain ⟨p, hp, rfl⟩ := List.mem_map.1 hτ
      exact fieldParams hD hR p hp] at ih
    exact .record hR ih
  | variant hT _ ih =>
    refine .variant hT fun c hc => ?_
    have h := ih c hc
    rw [List.map_append, map_substTys_of_params s (payloadParams hD hT c hc)] at h
    exact h
  | list m _ _ ih ihl =>
    refine .list m (fun n hn => ?_) ?_
    · have h := ih n hn
      rwa [List.map_append, List.map_replicate] at h
    · rwa [List.map_append, List.map_replicate] at ihl

end

end Stilt
