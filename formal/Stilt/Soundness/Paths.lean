import Stilt.Soundness.Values
import Stilt.Memory
import Stilt.Places

/-!
# Paths at run time

A place's path, once its indexes are evaluated, leads through values of the
types that typing gave its steps (`PathTyped`). Reading and writing along such
a path in a value of its type, or in a frame of its context, never gets stuck:
it reaches a value of the place's type, or panics on an index out of bounds
(effects.panic-kinds; std.lists). A write keeps the value's type and the
frame's.
-/

namespace Stilt

section

variable {D : Decls}

/-- Following a path from a value of run-time type `σ` reaches one of type
`σ'`: each field step is a field of a record type, at the type's run-time arguments
(types.field-access), and each index step an element of a list (std.lists). -/
inductive PathTyped (D : Decls) : STy → Path → STy → Prop
  | nil {σ : STy} : PathTyped D σ [] σ
  | field {R : Name} {as : List STy} {r : RecordDecl} {f : Name} {τ : Ty} {p : Path} {σ' : STy} :
      D.record? R = some r → r.fields.lookup f = some τ →
      PathTyped D (τ.semAt (r.typeParams.zip as)) p σ' →
      PathTyped D (.record R as) (.field f :: p) σ'
  | index {σ : STy} {k : Int} {p : Path} {σ' : STy} :
      PathTyped D σ p σ' → PathTyped D (.list σ) (.index k :: p) σ'
  /-- A tuple field is the element at its position (types.field-access). -/
  | elem {σs : List STy} {f : Name} {σ : STy} {p : Path} {σ' : STy} :
      (positions σs).lookup f = some σ → PathTyped D σ p σ' →
      PathTyped D (.tuple σs) (.field f :: p) σ'

theorem Fields.Typed.lookup :
    ∀ {fields : List (Name × Value)} {declared : List (Name × Ty)} {π : SParams} {f : Name}
      {τ : Ty}, Fields.Typed D fields declared π → declared.lookup f = some τ →
        ∃ v, fields.lookup f = some v ∧ Value.Typed D v (τ.semAt π)
  | _, _, _, _, _, .nil, h => nomatch h
  | _, _, _, f, _, .cons (f := g) hv hrest, h => by
    by_cases hfg : f = g
    · subst hfg
      simp only [List.lookup_cons_self, Option.some.injEq] at h ⊢
      exact ⟨_, rfl, h ▸ hv⟩
    · rw [lookup_cons_ne hfg] at h ⊢
      exact Fields.Typed.lookup hrest h

theorem Fields.Typed.assocSet {u : Value} {f : Name} {τ : Ty} {π : SParams}
    (hu : Value.Typed D u (τ.semAt π)) :
    ∀ {fields : List (Name × Value)} {declared : List (Name × Ty)},
      Fields.Typed D fields declared π → declared.lookup f = some τ →
        Fields.Typed D (Stilt.assocSet fields f u) declared π
  | _, _, .nil, _ => .nil
  | _, _, .cons (f := g) hv hrest, h => by
    by_cases hfg : f = g
    · subst hfg
      simp only [List.lookup_cons_self, Option.some.injEq] at h
      subst h
      simpa [Stilt.assocSet] using Fields.Typed.cons hu hrest
    · rw [lookup_cons_ne hfg] at h
      simpa [Stilt.assocSet, hfg] using Fields.Typed.cons hv (Fields.Typed.assocSet hu hrest h)

theorem elemAt?_mem {vs : List Value} {k : Int} {v : Value} (h : elemAt? vs k = some v) : v ∈ vs := by
  unfold elemAt? at h
  split at h
  · exact List.mem_of_getElem? h
  · cases h

/-- A read along a typed path reaches a value of its type, or panics. -/
theorem PathTyped.get {σ σ' : STy} {p : Path} (hp : PathTyped D σ p σ') :
    ∀ {v : Value}, Value.Typed D v σ →
      (∃ w, v.get p = .ok w ∧ Value.Typed D w σ') ∨ v.get p = .error (.panic .bounds) := by
  induction hp with
  | nil => intro v hv; exact .inl ⟨v, rfl, hv⟩
  | field hR hf _ ih =>
    intro v hv
    obtain ⟨r', fields, rfl, hR', -, hfs⟩ := hv.record_inv
    obtain rfl := Option.some.inj (hR'.symm.trans hR)
    obtain ⟨u, hu, hut⟩ := hfs.lookup hf
    simpa [Value.get, hu] using ih hut
  | @index _ k _ _ _ ih =>
    intro v hv
    obtain ⟨vs, rfl, hvs⟩ := hv.list_inv
    cases he : elemAt? vs k with
    | none => exact .inr (by simp [Value.get, he])
    | some u => simpa [Value.get, he] using ih (hvs u (elemAt?_mem he))
  | elem hf _ ih =>
    intro v hv
    obtain ⟨vs, rfl, hvs⟩ := hv.tuple_inv
    obtain ⟨u, hu, hut⟩ := lookup_positionsFrom_forall₂ 0 _ hvs.forall₂ hf
    simpa [Value.tuple, positions, Value.get, hu] using ih hut

/-- A write along a typed path keeps the value's type, or panics. -/
theorem PathTyped.set {σ σ' : STy} {p : Path} (hp : PathTyped D σ p σ') {w : Value}
    (hw : Value.Typed D w σ') :
    ∀ {v : Value}, Value.Typed D v σ →
      (∃ v', v.set p w = .ok v' ∧ Value.Typed D v' σ) ∨ v.set p w = .error (.panic .bounds) := by
  induction hp with
  | nil => intro v _; exact .inl ⟨w, rfl, hw⟩
  | field hR hf _ ih =>
    intro v hv
    obtain ⟨r', fields, rfl, hR', hl, hfs⟩ := hv.record_inv
    obtain rfl := Option.some.inj (hR'.symm.trans hR)
    obtain ⟨u, hu, hut⟩ := hfs.lookup hf
    rcases ih hw hut with ⟨u', hset, hu'⟩ | hset
    · exact .inl ⟨_, by simp [Value.set, hu, hset]; rfl, .record hR' hl (hfs.assocSet hu' hf)⟩
    · exact .inr (by simp [Value.set, hu, hset]; rfl)
  | @index _ k _ _ _ ih =>
    intro v hv
    obtain ⟨vs, rfl, hvs⟩ := hv.list_inv
    cases he : elemAt? vs k with
    | none => exact .inr (by simp [Value.set, he])
    | some u =>
      rcases ih hw (hvs u (elemAt?_mem he)) with ⟨u', hset, hu'⟩ | hset
      · refine .inl ⟨_, by simp [Value.set, he, hset]; rfl, .list fun x hx => ?_⟩
        rcases List.mem_or_eq_of_mem_set hx with hx | rfl
        · exact hvs x hx
        · exact hu'
      · exact .inr (by simp [Value.set, he, hset]; rfl)
  | elem hf _ ih =>
    intro v hv
    obtain ⟨vs, rfl, hvs⟩ := hv.tuple_inv
    obtain ⟨u, hu, hut⟩ := lookup_positionsFrom_forall₂ 0 _ hvs.forall₂ hf
    rcases ih hw hut with ⟨u', hset, hu'⟩ | hset
    · obtain ⟨vs', hvs', htyped⟩ := assocSet_positionsFrom_forall₂ 0 _ hvs.forall₂ hf hu'
      refine .inl ⟨.tuple vs', ?_, .tuple (Elems.Typed.of_forall₂ htyped)⟩
      simp only [Value.tuple, positions, Value.set, hu, hset]
      show Except.ok (Value.record tupleName (assocSet (positionsFrom 0 vs) _ u')) = _
      rw [hvs']
    · exact .inr (by simp [Value.tuple, positions, Value.set, hu, hset]; rfl)

/-! ## Frames -/

theorem Frame.Typed.lookup :
    ∀ {γ : List (Name × Value)} {Γ : Ctx} {η : REnv} {x : Name} {b : Binding},
      Frame.Typed D γ Γ η → Γ.lookup x = some b →
        ∃ v, γ.lookup x = some v ∧ Value.Typed D v (b.type.close η)
  | _, _, _, _, _, .nil, h => nomatch h
  | _, _, _, x, _, .cons (x := y) hv hrest, h => by
    by_cases hxy : x = y
    · subst hxy
      simp only [Ctx.lookup, List.lookup_cons_self, Option.some.injEq] at h ⊢
      exact ⟨_, rfl, h ▸ hv⟩
    · simp only [Ctx.lookup] at h
      rw [lookup_cons_ne hxy] at h ⊢
      exact Frame.Typed.lookup hrest h

theorem Frame.Typed.assocSet {x : Name} {v : Value} :
    ∀ {γ : List (Name × Value)} {Γ : Ctx} {η : REnv} {b : Binding},
      Frame.Typed D γ Γ η → Γ.lookup x = some b → Value.Typed D v (b.type.close η) →
        Frame.Typed D (Stilt.assocSet γ x v) Γ η
  | _, _, _, _, .nil, _, _ => .nil
  | _, _, _, _, .cons (x := y) hw hrest, h, hv => by
    by_cases hxy : x = y
    · subst hxy
      simp only [Ctx.lookup, List.lookup_cons_self, Option.some.injEq] at h
      subst h
      simpa [Stilt.assocSet] using Frame.Typed.cons hv hrest
    · simp only [Ctx.lookup] at h
      rw [lookup_cons_ne hxy] at h
      simpa [Stilt.assocSet, hxy] using Frame.Typed.cons hw (Frame.Typed.assocSet hrest h hv)

/-- Reading a place of a typed frame reaches a value of its type, or panics. -/
theorem Frame.Typed.read {γ : List (Name × Value)} {Γ : Ctx} {η : REnv} {x : Name} {b : Binding}
    {p : Path} {σ' : STy} (hγ : Frame.Typed D γ Γ η) (hx : Γ.lookup x = some b)
    (hp : PathTyped D (b.type.close η) p σ') :
    (∃ w, Copy.read γ x p = .ok w ∧ Value.Typed D w σ') ∨
      Copy.read γ x p = .error (.panic .bounds) := by
  obtain ⟨v, hv, hvt⟩ := hγ.lookup hx
  simpa [Copy.read, hv] using hp.get hvt

/-- Writing a place of a typed frame keeps the frame typed, or panics. -/
theorem Frame.Typed.write {γ : List (Name × Value)} {Γ : Ctx} {η : REnv} {x : Name} {b : Binding}
    {p : Path} {σ' : STy} {w : Value} (hγ : Frame.Typed D γ Γ η) (hx : Γ.lookup x = some b)
    (hp : PathTyped D (b.type.close η) p σ') (hw : Value.Typed D w σ') :
    (∃ γ', Copy.write γ x p w = .ok γ' ∧ Frame.Typed D γ' Γ η) ∨
      Copy.write γ x p w = .error (.panic .bounds) := by
  obtain ⟨v, hv, hvt⟩ := hγ.lookup hx
  rcases hp.set hw hvt with ⟨v', hset, hv'⟩ | hset
  · exact .inl ⟨_, by simp [Copy.write, hv, hset]; rfl, hγ.assocSet hx hv'⟩
  · exact .inr (by simp [Copy.write, hv, hset]; rfl)

end

end Stilt
