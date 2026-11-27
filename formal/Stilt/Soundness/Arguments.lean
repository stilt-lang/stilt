import Stilt.Soundness.Close

/-!
# Type arguments at run time

A generic record or variant type's fields and payloads are declared in terms of its type
parameters (declarations.type-parameters), and a value of an instance has them at the
instance's arguments. At run time the arguments are run-time types, so a field's type at
run time is its declared type, read with no row variable, since it has none, with the type
parameters replaced by the run-time arguments (`STy.substParams`). Reading a type after its
type parameters are instantiated is reading it, then replacing them by the arguments read
(`Ty.close_substTys`), and equivalent arguments give equivalent types
(`STy.substParams_eqv`).
-/

namespace Stilt

/-- What the type parameters of a declaration stand for at run time: the run-time types of
a use's type arguments. -/
abbrev SParams := List (Name × STy)

mutual

/-- Replaces the type parameters of a run-time type by what `π` gives them. A row's error
types are left as they are: a declaration's rows name no type parameter. -/
def STy.substParams (π : SParams) : STy → STy
  | .param T => (π.lookup T).getD (.param T)
  | .record R as => .record R (STys.substParams π as)
  | .variant T as => .variant T (STys.substParams π as)
  | .list a => .list (a.substParams π)
  | .tuple as => .tuple (STys.substParams π as)
  | .map a b => .map (a.substParams π) (b.substParams π)
  | .set a => .set (a.substParams π)
  | .shared a => .shared (a.substParams π)
  | .fn ps r R => .fn (SParamTys.substParams π ps) (r.substParams π) R
  | a => a

/-- Replaces the type parameters of a list of run-time types. -/
def STys.substParams (π : SParams) : List STy → List STy
  | [] => []
  | a :: as => a.substParams π :: STys.substParams π as

/-- Replaces the type parameters of a list of run-time parameter types. -/
def SParamTys.substParams (π : SParams) : List (Mode × STy) → List (Mode × STy)
  | [] => []
  | (m, a) :: ps => (m, a.substParams π) :: SParamTys.substParams π ps

end

/-- A declared type at run time, at the run-time arguments `π` of its declaration's type
parameters: its closed reading, with the parameters replaced. -/
def Ty.semAt (π : SParams) (τ : Ty) : STy := τ.sem.substParams π

/-! ## Reading an instance -/

mutual

/-- Instantiating a type's parameters, then reading it, is reading it, then replacing its
parameters by the arguments read. -/
theorem Ty.close_substTys (s : TySubst) (η : REnv) :
    ∀ τ : Ty, (τ.substTys s).close η = (τ.close η).substParams (s.map (Prod.map id (Ty.close η)))
  | .int _ | .float _ | .bool | .str | .unit | .never => rfl
  | .param T => by
    simp only [Ty.substTys, Ty.close, STy.substParams, lookup_map_snd]
    cases s.lookup T <;> rfl
  | .record R τs => by
    simp only [Ty.substTys, Ty.close, STy.substParams, closeTys_substTys s η τs]
  | .variant T τs => by
    simp only [Ty.substTys, Ty.close, STy.substParams, closeTys_substTys s η τs]
  | .list τ => by simp only [Ty.substTys, Ty.close, STy.substParams, Ty.close_substTys s η τ]
  | .tuple τs => by
    simp only [Ty.substTys, Ty.close, STy.substParams, closeTys_substTys s η τs]
  | .map κ τ => by
    simp only [Ty.substTys, Ty.close, STy.substParams, Ty.close_substTys s η κ,
      Ty.close_substTys s η τ]
  | .set τ => by simp only [Ty.substTys, Ty.close, STy.substParams, Ty.close_substTys s η τ]
  | .view τ => by simp only [Ty.substTys, Ty.close, Ty.close_substTys s η τ]
  | .shared τ => by simp only [Ty.substTys, Ty.close, STy.substParams, Ty.close_substTys s η τ]
  | .fn ps r ρ => by
    simp only [Ty.substTys, Ty.close, STy.substParams, closeParams_substTys s η ps,
      Ty.close_substTys s η r]

theorem closeTys_substTys (s : TySubst) (η : REnv) :
    ∀ τs : List Ty, closeTys η (substTyList s τs) =
      STys.substParams (s.map (Prod.map id (Ty.close η))) (closeTys η τs)
  | [] => rfl
  | τ :: τs => by
    simp only [substTyList, closeTys, STys.substParams, Ty.close_substTys s η τ,
      closeTys_substTys s η τs]

theorem closeParams_substTys (s : TySubst) (η : REnv) :
    ∀ ps : List (Mode × Ty), closeParams η (substParamTys s ps) =
      SParamTys.substParams (s.map (Prod.map id (Ty.close η))) (closeParams η ps)
  | [] => rfl
  | (_, τ) :: ps => by
    simp only [substParamTys, closeParams, SParamTys.substParams, Ty.close_substTys s η τ,
      closeParams_substTys s η ps]

end

/-- A closed declared type, instantiated by a use's arguments and read, is its reading at
the arguments read. -/
theorem Ty.Closed.close_substTys {τ : Ty} (h : τ.Closed) (names : List Name) (τs : List Ty)
    (η : REnv) : (τ.substTys (names.zip τs)).close η = τ.semAt (names.zip (closeTys η τs)) := by
  rw [Ty.close_substTys, h.close η, Ty.semAt, closeTys_eq_map, List.zip_map_right]

/-! ## Equivalent arguments -/

theorem STysEqv.length : ∀ {as bs : List STy}, STysEqv as bs → as.length = bs.length
  | _, _, .nil => rfl
  | _, _, .cons _ h => by simp [STysEqv.length h]

/-- Arguments that pair the same parameters with equivalent run-time types. -/
def SParams.Eqv (π π' : SParams) : Prop := Forall₂ (fun p q => p.1 = q.1 ∧ p.2.Eqv q.2) π π'

theorem SParams.Eqv.lookup {π π' : SParams} (h : π.Eqv π') (T : Name) :
    (π.lookup T = none ∧ π'.lookup T = none) ∨
      ∃ a b, π.lookup T = some a ∧ π'.lookup T = some b ∧ a.Eqv b := by
  unfold SParams.Eqv at h
  induction h with
  | nil => exact .inl ⟨rfl, rfl⟩
  | @cons p q _ _ hpq _ ih =>
    obtain ⟨T', a⟩ := p
    obtain ⟨U, b⟩ := q
    obtain ⟨rfl, hab⟩ := hpq
    simp only [List.lookup_cons]
    split
    · exact .inr ⟨a, b, rfl, rfl, hab⟩
    · exact ih

theorem SParams.Eqv.zip (names : List Name) :
    ∀ {as bs : List STy}, STysEqv as bs → SParams.Eqv (names.zip as) (names.zip bs)
  | _, _, .nil => by cases names <;> exact .nil
  | _, _, .cons h hs => by
    cases names with
    | nil => exact .nil
    | cons n names => exact .cons ⟨rfl, h⟩ (SParams.Eqv.zip names hs)

mutual

/-- Equivalent arguments give equivalent types. -/
theorem STy.substParams_eqv {π π' : SParams} (h : π.Eqv π') :
    ∀ a : STy, (a.substParams π).Eqv (a.substParams π')
  | .param T => by
    simp only [STy.substParams]
    rcases h.lookup T with ⟨h₁, h₂⟩ | ⟨a, b, h₁, h₂, hab⟩
    · rw [h₁, h₂]; exact .param T
    · rw [h₁, h₂]; exact hab
  | .record R as => .record R (STys.substParams_eqv h as)
  | .variant T as => .variant T (STys.substParams_eqv h as)
  | .list a => .list (STy.substParams_eqv h a)
  | .tuple as => .tuple (STys.substParams_eqv h as)
  | .map a b => .map (STy.substParams_eqv h a) (STy.substParams_eqv h b)
  | .set a => .set (STy.substParams_eqv h a)
  | .shared a => .shared (STy.substParams_eqv h a)
  | .fn ps r R =>
    .fn (SParamTys.substParams_eqv h ps) (STy.substParams_eqv h r) (Covers.refl R) (Covers.refl R)
  | .int k => .int k
  | .float k => .float k
  | .bool => .bool
  | .str => .str
  | .unit => .unit
  | .never => .never
  | .effect E => .effect E
  | .resume a r => .resume a r
  | .io => .io

theorem STys.substParams_eqv {π π' : SParams} (h : π.Eqv π') :
    ∀ as : List STy, STysEqv (STys.substParams π as) (STys.substParams π' as)
  | [] => .nil
  | a :: as => .cons (STy.substParams_eqv h a) (STys.substParams_eqv h as)

theorem SParamTys.substParams_eqv {π π' : SParams} (h : π.Eqv π') :
    ∀ ps : List (Mode × STy), SParamsEqv (SParamTys.substParams π ps) (SParamTys.substParams π' ps)
  | [] => .nil
  | (_, a) :: ps => .cons (STy.substParams_eqv h a) (SParamTys.substParams_eqv h ps)

end

theorem Ty.semAt_eqv {π π' : SParams} (h : π.Eqv π') (τ : Ty) : (τ.semAt π).Eqv (τ.semAt π') :=
  STy.substParams_eqv h τ.sem

mutual

/-- A declared type without type parameters reads as itself at no arguments. -/
theorem STy.substParams_nil : ∀ a : STy, a.substParams [] = a
  | .param _ | .int _ | .float _ | .bool | .str | .unit | .never | .effect _ | .resume _ _ | .io => rfl
  | .record R as => by rw [STy.substParams, STys.substParams_nil]
  | .variant T as => by rw [STy.substParams, STys.substParams_nil]
  | .list a => by rw [STy.substParams, STy.substParams_nil]
  | .tuple as => by rw [STy.substParams, STys.substParams_nil]
  | .map a b => by rw [STy.substParams, STy.substParams_nil, STy.substParams_nil]
  | .set a => by rw [STy.substParams, STy.substParams_nil]
  | .shared a => by rw [STy.substParams, STy.substParams_nil]
  | .fn ps r R => by rw [STy.substParams, SParamTys.substParams_nil, STy.substParams_nil]

theorem STys.substParams_nil : ∀ as : List STy, STys.substParams [] as = as
  | [] => rfl
  | a :: as => by rw [STys.substParams, STy.substParams_nil, STys.substParams_nil as]

theorem SParamTys.substParams_nil : ∀ ps : List (Mode × STy), SParamTys.substParams [] ps = ps
  | [] => rfl
  | (m, a) :: ps => by rw [SParamTys.substParams, STy.substParams_nil, SParamTys.substParams_nil ps]

end

end Stilt
