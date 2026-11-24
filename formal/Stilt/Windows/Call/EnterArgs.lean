import Stilt.Windows.Call.Settle
import Stilt.Windows.Watched
import Stilt.Windows.Guards.Call

/-!
# The parameters a call binds

Once a call's arguments are passed, the model of windows having kept each `let` argument for its
parameter's type, both models bind the same parameters to arguments of the same shapes
(`bindArgs`): values read alike, the in-place one a value the checks accept, each window of the
other watched by the reads around the call, and kept only for a parameter whose generic type
holds a view and is no function type, so whose binding's sources are its own place; and the same
places, whose shapes the reads around the call don't overlap (E0423).
-/

namespace Stilt

namespace Windows

open InPlace (Ref)

variable {D : Decls}

/-- The values a call's `let` parameters are bound to: the callee's `In`. -/
def inOf (bound : List (Name × Passed)) : List (Name × Value) :=
  bound.filterMap fun ya => ya.2.value?.map (ya.1, ·)

/-- Arguments once passed (the windows side after `passTo`), against the caller's context. -/
inductive PassRel (D : Decls) (c : Ctx) (si : IState) (sw : WState) :
    List Passed → List Passed → Prop
  | nil : PassRel D c si sw [] []
  | value {v w : Value} {ps ps' : List Passed} : VRel si.1.store sw.1.store w v → v.Viewed D →
      (∀ win ∈ windowsOf w, Watched c.R sw.1.env win) → PassRel D c si sw ps ps' →
      PassRel D c si sw (.value v :: ps) (.value w :: ps')
  | moved (x : Name) {v w : Value} {ps ps' : List Passed} : VRel si.1.store sw.1.store w v →
      v.Viewed D → (∀ win ∈ windowsOf w, Watched c.R sw.1.env win) →
      PassRel D c si sw ps ps' → PassRel D c si sw (.moved x v :: ps) (.moved x w :: ps')
  | place (x : Name) (p : Path) (ps₀ : List Projection) {ps ps' : List Passed} : p.Resolves ps₀ →
      unread c.R (Place.mk x ps₀).shape = true → PassRel D c si sw ps ps' →
      PassRel D c si sw (.place x p :: ps) (.place x p :: ps')

/-- A value passed that holds a window is one its parameter's type keeps. -/
def KeptFor (D : Decls) (params : List Param) (ps' : List Passed) : Prop :=
  ∀ (i : Nat) (p : Param) (a : Passed), params[i]? = some p → ps'[i]? = some a → ∀ w, a.value? = some w → ¬Free w →
    keepsView D p.type = true

theorem KeptFor.tail {p : Param} {params : List Param} {a : Passed} {ps' : List Passed}
    (h : KeptFor D (p :: params) (a :: ps')) : KeptFor D params ps' :=
  fun i q b hq hb w hw hf => h (i + 1) q b hq hb w hw hf

/-- The sources a parameter's binding reads in the callee's scope. -/
def paramSources (D : Decls) (p : Param) : List Shape :=
  if p.type.holdsView D then p.viewSources else []

/-- A parameter whose instance type keeps views has a generic type whose binding reads its own
place. -/
theorem mem_paramSources {p₀ p : Param} (hi : ParamInst D p₀ p) (hk : keepsView D p.type = true) :
    (⟨p₀.name, []⟩ : Shape) ∈ paramSources D p₀ := by
  obtain ⟨-, -, hty, hfn⟩ := hi
  simp only [keepsView, Bool.and_eq_true] at hk
  have hh : p₀.type.holdsView D = true := hty.1 hk.1
  have hnf : p₀.type.isFn = false := by
    cases h : p₀.type.isFn
    · rfl
    · have := hfn h
      revert hk
      cases hp : p.type <;> simp_all [Ty.isFn]
  simp only [paramSources, hh, ↓reduceIte, Param.viewSources]
  cases hp : p₀.type <;> simp_all [Ty.isFn]

/-- The parameters a call binds, against the generic parameters: a `let` parameter bound to
values read alike, the in-place one a value the checks accept, each window of the other watched
and, if any, its binding reading its own place; an `inout` parameter bound to the same place, a
shape the reads don't overlap. -/
inductive BoundRel (D : Decls) (c : Ctx) (si : IState) (sw : WState) :
    List Param → List (Name × Passed) → List (Name × Passed) → Prop
  | nil : BoundRel D c si sw [] [] []
  | value {p₀ : Param} {ps₀ : List Param} {a a' : Passed} {v w : Value}
      {bs bs' : List (Name × Passed)} : a.value? = some v → a'.value? = some w →
      VRel si.1.store sw.1.store w v → v.Viewed D → (∀ win ∈ windowsOf w, Watched c.R sw.1.env win) →
      (¬Free w → (⟨p₀.name, []⟩ : Shape) ∈ paramSources D p₀) → p₀.mode = .let →
      BoundRel D c si sw ps₀ bs bs' →
      BoundRel D c si sw (p₀ :: ps₀) ((p₀.name, a) :: bs) ((p₀.name, a') :: bs')
  | place {p₀ : Param} {ps₀ : List Param} (x : Name) (q : Path) (qs : List Projection)
      {bs bs' : List (Name × Passed)} : q.Resolves qs → unread c.R (Place.mk x qs).shape = true →
      p₀.mode = .inout → BoundRel D c si sw ps₀ bs bs' →
      BoundRel D c si sw (p₀ :: ps₀) ((p₀.name, .place x q) :: bs) ((p₀.name, .place x q) :: bs')

theorem bindArgs_cons {p : Param} {params : List Param} {a : Passed} {args : List Passed}
    {bound : List (Name × Passed)} (h : bindArgs (p :: params) (a :: args) = some bound) :
    ∃ bs, bindArgs params args = some bs ∧ bound = (p.name, a) :: bs ∧
      ((p.mode = .let ∧ a.value?.isSome) ∨ (p.mode = .inout ∧ ∃ x q, a = .place x q)) := by
  unfold bindArgs at h
  split at h
  · obtain ⟨bs, hbs, rfl⟩ := Option.map_eq_some_iff.1 h
    exact ⟨bs, hbs, rfl, .inr ⟨by assumption, _, _, rfl⟩⟩
  · obtain ⟨bs, hbs, rfl⟩ := Option.map_eq_some_iff.1 h
    exact ⟨bs, hbs, rfl, .inl ⟨by assumption, rfl⟩⟩
  · obtain ⟨bs, hbs, rfl⟩ := Option.map_eq_some_iff.1 h
    exact ⟨bs, hbs, rfl, .inl ⟨by assumption, rfl⟩⟩
  · cases h

/-- Both models bind the parameters to related arguments. -/
theorem boundRel {c : Ctx} {si : IState} {sw : WState} :
    ∀ {ps ps' : List Passed}, PassRel D c si sw ps ps' → ∀ {params ps₀ : List Param}
      {bound bound' : List (Name × Passed)}, KeptFor D params ps' → ParamsInst D ps₀ params →
      bindArgs params ps = some bound → bindArgs params ps' = some bound' →
      BoundRel D c si sw ps₀ bound bound'
  | _, _, .nil, _, _, _, _, _, hi, hb, hb' => by
    cases hi with
    | nil => cases hb; cases hb'; exact .nil
    | cons _ _ => cases hb
  | _, _, .value hvw hv hwat h, _, _, _, _, hk, hi, hb, hb' => by
    cases hi with
    | nil => cases hb
    | cons hpi his =>
      obtain ⟨bs, hbs, rfl, hm⟩ := bindArgs_cons hb
      obtain ⟨bs', hbs', rfl, -⟩ := bindArgs_cons hb'
      have hname := hpi.2.1
      rw [hname]
      refine .value rfl rfl hvw hv hwat (fun hf => mem_paramSources hpi
        (hk 0 _ _ rfl rfl _ rfl hf)) ?_ (boundRel h hk.tail his hbs hbs')
      rcases hm with ⟨hm, -⟩ | ⟨-, x, q, hq⟩
      · rw [← hpi.1]; exact hm
      · cases hq
  | _, _, .moved z hvw hv hwat h, _, _, _, _, hk, hi, hb, hb' => by
    cases hi with
    | nil => cases hb
    | cons hpi his =>
      obtain ⟨bs, hbs, rfl, hm⟩ := bindArgs_cons hb
      obtain ⟨bs', hbs', rfl, -⟩ := bindArgs_cons hb'
      rw [hpi.2.1]
      refine .value rfl rfl hvw hv hwat (fun hf => mem_paramSources hpi
        (hk 0 _ _ rfl rfl _ rfl hf)) ?_ (boundRel h hk.tail his hbs hbs')
      rcases hm with ⟨hm, -⟩ | ⟨-, x, q, hq⟩
      · rw [← hpi.1]; exact hm
      · cases hq
  | _, _, .place x q qs hres hu h, _, _, _, _, hk, hi, hb, hb' => by
    cases hi with
    | nil => cases hb
    | cons hpi his =>
      obtain ⟨bs, hbs, rfl, hm⟩ := bindArgs_cons hb
      obtain ⟨bs', hbs', rfl, -⟩ := bindArgs_cons hb'
      rw [hpi.2.1]
      refine .place x q qs hres hu ?_ (boundRel h hk.tail his hbs hbs')
      rcases hm with ⟨-, hm⟩ | ⟨hm, -⟩
      · simp [Passed.value?] at hm
      · rw [← hpi.1]; exact hm

namespace BoundRel

variable {c : Ctx} {si : IState} {sw : WState}

/-- Each window of a value a `let` parameter is bound to holds, and the reads around the call
watch it. -/
theorem values : ∀ {ps₀ : List Param} {bs bs' : List (Name × Passed)},
    BoundRel D c si sw ps₀ bs bs' → ∀ ya ∈ bs', ∀ w, ya.2.value? = some w →
      ∀ win ∈ windowsOf w, Holds sw.1.store si.1.store win ∧ Watched c.R sw.1.env win
  | _, _, _, .nil, _, h, _, _, _, _ => nomatch h
  | _, _, _, .value _ hw hvw _ hwat _ _ h, ya, hya, w', hw', win, hwin => by
    rcases List.mem_cons.1 hya with rfl | hya
    · rw [hw, Option.some.injEq] at hw'
      subst hw'
      exact ⟨hvw.2 win hwin, hwat win hwin⟩
    · exact values h ya hya w' hw' win hwin
  | _, _, _, .place _ _ _ _ _ _ h, ya, hya, w', hw', win, hwin => by
    rcases List.mem_cons.1 hya with rfl | hya
    · cases hw'
    · exact values h ya hya w' hw' win hwin

/-- Each place an `inout` parameter is bound to has a shape the reads around the call don't
overlap, and the parameter is an `inout` one of the generic parameters. -/
theorem places : ∀ {ps₀ : List Param} {bs bs' : List (Name × Passed)},
    BoundRel D c si sw ps₀ bs bs' → ∀ y x q, (y, Passed.place x q) ∈ bs →
      (∃ qs, q.Resolves qs ∧ unread c.R (Place.mk x qs).shape = true) ∧
        ∃ p₀ ∈ ps₀, p₀.name = y ∧ p₀.mode = .inout
  | _, _, _, .nil, _, _, _, h => nomatch h
  | _, _, _, .value hv _ _ _ _ _ _ h, y, x, q, hm => by
    rcases List.mem_cons.1 hm with he | hm
    · injection he with _ he
      subst he
      cases hv
    · obtain ⟨h₁, p₀, hp₀, h₂⟩ := places h y x q hm
      exact ⟨h₁, p₀, List.mem_cons_of_mem _ hp₀, h₂⟩
  | _, _, _, .place (p₀ := p₀) x' q' qs hres hu hmode h, y, x, q, hm => by
    rcases List.mem_cons.1 hm with he | hm
    · injection he with h₁ h₂
      injection h₂ with h₃ h₄
      subst h₁ h₃ h₄
      exact ⟨⟨qs, hres, hu⟩, p₀, List.mem_cons_self, rfl, hmode⟩
    · obtain ⟨h₁, p₁, hp₁, h₂⟩ := places h y x q hm
      exact ⟨h₁, p₁, List.mem_cons_of_mem _ hp₁, h₂⟩

end BoundRel

theorem mem_inOf {bound : List (Name × Passed)} {y : Name} {w : Value} :
    (y, w) ∈ inOf bound ↔ ∃ a, (y, a) ∈ bound ∧ a.value? = some w := by
  simp only [inOf, List.mem_filterMap, Option.map_eq_some_iff, Prod.mk.injEq]
  constructor
  · rintro ⟨⟨y', a⟩, hm, w', hw, rfl, rfl⟩
    exact ⟨a, hm, hw⟩
  · rintro ⟨a, hm, hw⟩
    exact ⟨(y, a), hm, w, hw, rfl, rfl⟩

end Windows

end Stilt
