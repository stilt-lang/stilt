import Stilt.Instances.Patterns

/-!
# Fields of instances

The fields that a body knows a type to have, through a record or through a type parameter's
record bound (`FieldOf`), the instance has at the instance's type (records.record-bounds): so a
use's type arguments that meet the parameters' bounds meet them at the instance too, and a read
or a write through a record bound is, at the instance, one of the record that the parameter
stands for or one through another parameter's bound.
-/

namespace Stilt

section

variable {D : Decls} {scope scope' : RowScope} {s : TySubst}

/-- A field that a body knows a type to have, the instance has at the instance's type. -/
theorem FieldOf.substTys (hD : D.WellFormed) (hs : s.Fits D scope scope') {τ T : Ty} {f : Name}
    (h : FieldOf D scope τ f T) : FieldOf D scope' (τ.substTys s) f (T.substTys s) := by
  rcases h with ⟨R, args, r, rfl, hR, hlen, hfl⟩ | ⟨p, hp, rfl, hpl⟩
  · refine .inl ⟨R, args.map (Ty.substTys s), r, ?_, hR, by rw [List.length_map]; exact hlen,
      hD.lookup_fieldsAt_substTys s hR hlen hfl⟩
    simp [Ty.substTys, substTyList_eq_map]
  · obtain ⟨σ, hl, -⟩ := hs.covers p hp
    have hsub : (Ty.param p.name).substTys s = σ := by simp [Ty.substTys, hl]
    rw [hsub]
    exact hs.records p hp σ hl (f, T) (mem_of_lookup hpl)

theorem TySubst.Fits.typeArgs (hD : D.WellFormed) (hs : s.Fits D scope scope') {ps : List TypeParam} {τs : List Ty}
    (h : TypeArgsFit D scope ps τs) : TypeArgsFit D scope' ps (τs.map (Ty.substTys s)) := by
  have hlen := h.length_eq
  unfold TypeArgsFit at h ⊢
  have hz : TySubst.then ((ps.map TypeParam.name).zip τs) s =
      (ps.map TypeParam.name).zip (τs.map (Ty.substTys s)) := TySubst.then_zip _ _ _
  refine Forall₂.imp_map (fun _ _ hx => ⟨hx.1.substTys hs.ground, hs.wellFormed hx.2.1, fun B hB =>
    ⟨hs.satisfies hD (hx.2.2.1 B hB).1, fun args ha => ⟨((hx.2.2.1 B hB).2 args ha).1, ?_⟩⟩,
    fun fT hfT => ⟨(hx.2.2.2 fT hfT).1, ?_⟩⟩) h
  · have h' := ((hx.2.2.1 B hB).2 args ha).2.substTys hD hs
    rw [List.map_map] at h'
    rwa [List.map_congr_left fun a hm => by
      rw [Function.comp_apply, Ty.substTys_substTys _ _ _ fun T hT =>
        List.lookup_zip_isSome (((hx.2.2.1 B hB).2 args ha).1 a hm T hT) (by simpa using hlen.symm),
        hz]] at h'
  · have h' := (hx.2.2.2 fT hfT).2.substTys hD hs
    rwa [Ty.substTys_substTys _ _ _ fun T hT =>
      List.lookup_zip_isSome ((hx.2.2.2 fT hfT).1 T hT) (by simpa using hlen.symm), hz] at h'

/-- A field read through a record bound, instantiated: the instance of the parameter has the
field, a record's or one its own bound names (records.record-bounds). -/
theorem HasType.boundField_substTys (hs : s.Fits D scope scope') {Γ : Ctx} {fx : Effects}
    {e : Expr} {p : TypeParam} {f : Name} {τ : Ty} (hp : p ∈ scope.types)
    (h : HasType D scope' Γ fx e ((Ty.param p.name).substTys s)) (hf : p.fields.lookup f = some τ) :
    HasType D scope' Γ fx (.field e f) (τ.substTys s) := by
  obtain ⟨σ, hl, -⟩ := hs.covers p hp
  have hsub : (Ty.param p.name).substTys s = σ := by simp [Ty.substTys, hl]
  rw [hsub] at h
  rcases hs.records p hp σ hl (f, τ) (mem_of_lookup hf) with ⟨R, args, r, rfl, hR, hlen, hfl⟩ |
    ⟨q, hq, rfl, hql⟩
  · exact .field h hR hlen hfl
  · exact .boundField hq h hql

/-- A field written through a record bound, instantiated. -/
theorem PathFits.boundField_substTys (hs : s.Fits D scope scope') {Γ : Ctx} {fx : Effects}
    {p : TypeParam} {f : Name} {path : List Projection} {τ τ' : Ty} (hq : p ∈ scope.types)
    (hf : p.fields.lookup f = some τ)
    (h : PathFits D scope' Γ fx (τ.substTys s) path τ') :
    PathFits D scope' Γ fx ((Ty.param p.name).substTys s) (.field f :: path) τ' := by
  obtain ⟨σ, hl, -⟩ := hs.covers p hq
  have hsub : (Ty.param p.name).substTys s = σ := by simp [Ty.substTys, hl]
  rw [hsub]
  rcases hs.records p hq σ hl (f, τ) (mem_of_lookup hf) with ⟨R, args, r, rfl, hR, hlen, hfl⟩ |
    ⟨q, hq', rfl, hql⟩
  · exact .field hR hlen hfl h
  · exact .boundField hq' hql h

/-- A tuple's element, instantiated. -/
theorem HasType.elem_substTys {Γ : Ctx} {fx : Effects} {e : Expr} {τs : List Ty} {f : Name}
    {τ : Ty} (h : HasType D scope' Γ fx e ((Ty.tuple τs).substTys s))
    (hf : (positions τs).lookup f = some τ) : HasType D scope' Γ fx (.field e f) (τ.substTys s) := by
  simp only [Ty.substTys, substTyList_eq_map] at h
  exact .elem h (by unfold positions at hf ⊢; rw [lookup_positionsFrom_map, hf]; rfl)

/-- A field read, instantiated: the field's type at the arguments' instances. -/
theorem HasType.field_substTys (hD : D.WellFormed) {Γ : Ctx} {fx : Effects} {e : Expr} {R f : Name}
    {args : List Ty} {r : RecordDecl} {τ : Ty}
    (h : HasType D scope' Γ fx e ((Ty.record R args).substTys s)) (hR : D.record? R = some r)
    (hlen : args.length = r.typeParams.length) (hf : (r.fieldsAt args).lookup f = some τ) :
    HasType D scope' Γ fx (.field e f) (τ.substTys s) := by
  simp only [Ty.substTys, substTyList_eq_map] at h
  exact .field h hR (by rw [List.length_map]; exact hlen) (hD.lookup_fieldsAt_substTys s hR hlen hf)

end

end Stilt
