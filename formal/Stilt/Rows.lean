import Stilt.Rows.Types

/-!
# Rows

The instantiation of row variables in an expression, at a use (effects.row-variables and
effects.inference), and the lemmas on rows and on fitting types (effects.missing-effects,
effects.function-value-unions and effects.function-values).
-/

namespace Stilt

mutual

/-- Replaces the row variables in every type an expression writes. A call
applies its instantiation to the body of the function it calls, as a call of
a generic function instantiates its body in the elaborated program. Only
functions declare row variables (effects.row-variables), so nothing inside a body
binds one. -/
def Expr.substRows (s : RowSubst) : Expr → Expr
  | .var x => .var x
  | .move x => .move x
  | .int n => .int n
  | .bool b => .bool b
  | .unit => .unit
  | .record R τs fields => .record R (substTysRows s τs) (substFieldRows s fields)
  | .variant T τs C es => .variant T (substTysRows s τs) C (substExprRows s es)
  | .list τ es => .list (τ.substRows s) (substExprRows s es)
  | .op o es => .op o (substExprRows s es)
  | .view es => .view (substExprRows s es)
  | .field e f => .field (e.substRows s) f
  | .index e i => .index (e.substRows s) (i.substRows s)
  | .fnRef f tys rows => .fnRef f (substTysRows s tys) (rows.map (Row.substRows s))
  | .method t m τ => .method t m (τ.substRows s)
  | .closure ps r ρ body =>
    .closure (ps.map (Param.substRows s)) (r.substRows s) (ρ.substRows s) (body.substRows s)
  | .call f args τ => .call (f.substRows s) (substArgRows s args) τ
  | .letIn x τ e body => .letIn x (τ.substRows s) (e.substRows s) (body.substRows s)
  | .varIn x τ e body => .varIn x (τ.substRows s) (e.substRows s) (body.substRows s)
  | .assign ⟨x, path⟩ e => .assign ⟨x, substPathRows s path⟩ (e.substRows s)
  | .seq a b => .seq (a.substRows s) (b.substRows s)
  | .if c τ a b => .if (c.substRows s) (τ.substRows s) (a.substRows s) (b.substRows s)
  | .match e τ arms => .match (e.substRows s) (τ.substRows s) (substArmRows s arms)
  | .for x τ e body => .for x (τ.substRows s) (e.substRows s) (body.substRows s)
  | .raise e => .raise (e.substRows s)
  | .try e => .try (e.substRows s)
  | .form fm e => .form fm (e.substRows s)
  | .tryCatch e E x h τ =>
    .tryCatch (e.substRows s) (E.substRows s) x (h.substRows s) (τ.substRows s)
  | .while c body => .while (c.substRows s) (body.substRows s)
  | .loop body => .loop (body.substRows s)
  | .break => .break
  | .continue => .continue
  | .return e => .return (e.substRows s)
  | .perform op e => .perform op (e.substRows s)
  | .withH E c h b => .withH E c (h.substRows s) (b.substRows s)
  | .held ns hs body =>
    .held (ns.map fun p => (p.1, p.2.substRows s)) (substExprRows s hs) (body.substRows s)

/-- Replaces the row variables in a list of expressions. -/
def substExprRows (s : RowSubst) : List Expr → List Expr
  | [] => []
  | e :: es => e.substRows s :: substExprRows s es

/-- Replaces the row variables in the fields of a record literal. -/
def substFieldRows (s : RowSubst) : List (Name × Expr) → List (Name × Expr)
  | [] => []
  | (f, e) :: fields => (f, e.substRows s) :: substFieldRows s fields

/-- Replaces the row variables in the arguments of a call. -/
def substArgRows (s : RowSubst) : List Arg → List Arg
  | [] => []
  | .value e :: args => .value (e.substRows s) :: substArgRows s args
  | .inout ⟨x, path⟩ :: args => .inout ⟨x, substPathRows s path⟩ :: substArgRows s args

/-- Replaces the row variables in the indexes of a place. -/
def substPathRows (s : RowSubst) : List Projection → List Projection
  | [] => []
  | .field f :: path => .field f :: substPathRows s path
  | .index i :: path => .index (i.substRows s) :: substPathRows s path

/-- Replaces the row variables in the arms of a `match`. -/
def substArmRows (s : RowSubst) : List Arm → List Arm
  | [] => []
  | ⟨C, binders, body⟩ :: arms => ⟨C, binders, body.substRows s⟩ :: substArmRows s arms

end

/-! ## Lemmas -/

theorem length_substExprRows (s : RowSubst) : ∀ es : List Expr, (substExprRows s es).length = es.length
  | [] => rfl
  | _ :: es => by simp [substExprRows, length_substExprRows s es]

theorem substTysRows_eq_map (s : RowSubst) : ∀ τs : List Ty, substTysRows s τs = τs.map (Ty.substRows s)
  | [] => rfl
  | τ :: τs => by simp [substTysRows, substTysRows_eq_map s τs]

namespace Row

@[simp] theorem pure_io : pure.io = false := rfl
@[simp] theorem pure_raise : pure.raise = none := rfl
@[simp] theorem pure_vars : pure.vars = [] := rfl

theorem Within.refl (ρ : Row) : ρ.Within ρ :=
  ⟨id, fun _ => id, fun _ => id, fun _ => id, fun _ => id⟩

theorem Within.trans {a b c : Row} (h₁ : a.Within b) (h₂ : b.Within c) :
    a.Within c :=
  ⟨h₂.io ∘ h₁.io, fun E h => h₂.raise E (h₁.raise E h),
    fun v h => h₂.vars v (h₁.vars v h), fun E h => h₂.effects E (h₁.effects E h),
    fun p h => h₂.resume p (h₁.resume p h)⟩

/-- A pure function fits any row (effects.function-values). -/
theorem pure_within (ρ : Row) : pure.Within ρ :=
  ⟨fun h => absurd h (by simp), fun _ h => absurd h (by simp),
    fun _ h => absurd h (by simp), fun _ h => absurd h (by simp [pure]),
    fun _ h => absurd h (by simp [pure])⟩

/-- Rows are their elements: two rows that fit within each other have the same
elements. -/
theorem Within.antisymm {a b : Row} (h₁ : a.Within b) (h₂ : b.Within a) :
    a.Same b := by
  refine ⟨?_, ?_, fun v => ⟨h₁.vars v, h₂.vars v⟩, fun E => ⟨h₁.effects E, h₂.effects E⟩, ?_⟩
  · cases ha : a.io <;> cases hb : b.io <;> first
      | rfl
      | exact absurd (h₁.io ha) (by simp [hb])
      | exact absurd (h₂.io hb) (by simp [ha])
  · cases ha : a.raise with
    | some E => exact (h₁.raise E ha).symm
    | none =>
      cases hb : b.raise with
      | none => rfl
      | some E => exact absurd (h₂.raise E hb) (by simp [ha])
  · cases ha : a.resume with
    | some p => exact (h₁.resume p ha).symm
    | none =>
      cases hb : b.resume with
      | none => rfl
      | some p => exact absurd (h₂.resume p hb) (by simp [ha])

/-- Rows with the same elements fit within each other. -/
theorem Same.within {a b : Row} (h : a.Same b) : a.Within b :=
  ⟨fun h' => h.io ▸ h', fun _ h' => h.raise ▸ h', fun v h' => (h.vars v).1 h',
    fun E h' => (h.effects E).1 h', fun _ h' => h.resume ▸ h'⟩

/-- A row fits within the row of a `catch` operand built from it, except for
its own `raise` label, which the `catch` replaces (effects.catch). -/
theorem Within.withRaise {a ρ : Row} (E : Ty) (h : a.Within ρ)
    (hraise : a.raise = none ∨ a.raise = some E) : a.Within (ρ.withRaise E) := by
  refine ⟨h.io, fun E' hE' => ?_, h.vars, h.effects, h.resume⟩
  rcases hraise with h' | h'
  · rw [h'] at hE'
    exact nomatch hE'
  · rw [h'] at hE'
    cases hE'
    rfl

theorem within_union_left (a b : Row) : a.Within (union a b) := by
  refine ⟨fun h => by simp [union, h], fun E h => ?_, fun v h => ?_, fun E h => ?_, fun p h => ?_⟩
  · simp [union, h]
  · simp [union, h]
  · simp [union, h]
  · simp [union, h]

theorem within_union_right {a b : Row} (h : Compatible a b) :
    b.Within (union a b) := by
  refine ⟨fun h' => by simp [union, h'], fun E hE => ?_, fun v hv => ?_, fun E hE => ?_,
    fun p hp => ?_⟩
  · cases ha : a.raise with
    | none => simp [union, ha, hE]
    | some E' => simp [union, ha, h.raise E' E ha hE]
  · simp [union, hv]
  · simp [union, hE]
  · cases ha : a.resume with
    | none => simp [union, ha, hp]
    | some p' => simp [union, ha, h.resume p' p ha hp]

/-- The union of two rows fits within every row that both fit within. -/
theorem union_within {a b c : Row} (ha : a.Within c) (hb : b.Within c) :
    (union a b).Within c := by
  refine ⟨fun h => ?_, fun E hE => ?_, fun v hv => ?_, fun E hE => ?_, fun p hp => ?_⟩
  · simp only [union, Bool.or_eq_true] at h
    exact h.elim ha.io hb.io
  · cases h : a.raise with
    | some E' =>
      simp [union, h] at hE
      exact hE ▸ ha.raise E' h
    | none =>
      simp [union, h] at hE
      exact hb.raise E hE
  · simp only [union, List.mem_append] at hv
    exact hv.elim (ha.vars v) (hb.vars v)
  · simp only [union, List.mem_append] at hE
    exact hE.elim (ha.effects E) (hb.effects E)
  · cases h : a.resume with
    | some p' =>
      simp [union, h] at hp
      exact hp ▸ ha.resume p' h
    | none =>
      simp [union, h] at hp
      exact hb.resume p hp

/-- The common row of two branches does not depend on their order (effects.function-value-unions). -/
theorem union_comm {a b : Row} (h : Compatible a b) : (union a b).Same (union b a) :=
  Within.antisymm
    (union_within (within_union_right ⟨fun E E' h₁ h₂ => (h.raise E' E h₂ h₁).symm,
      fun p p' h₁ h₂ => (h.resume p' p h₂ h₁).symm⟩)
      (within_union_left b a))
    (union_within (within_union_right h) (within_union_left a b))

end Row

namespace Fits

theorem trans {a b c : Ty} (h₁ : Fits a b) (h₂ : Fits b c) : Fits a c := by
  cases h₁ with
  | refl => exact h₂
  | never => exact .never c
  | fn hab =>
    cases h₂ with
    | refl => exact .fn hab
    | fn hbc => exact .fn (hab.trans hbc)

/-- Only `()` and `Never` fit `()`. So a statement before the last one of its
block, and the body of a loop, have one of these types (expressions.statements). -/
theorem unit_iff {σ : Ty} : Fits σ .unit ↔ σ = .unit ∨ σ = .never := by
  constructor
  · intro h
    cases h with
    | refl => exact .inl rfl
    | never => exact .inr rfl
  · rintro (rfl | rfl)
    · exact .refl _
    · exact .never _

/-- A tuple type fits only itself, as a list type does (effects.function-values). -/
theorem tuple_iff {σ : Ty} {τs : List Ty} : Fits σ (.tuple τs) ↔ σ = .tuple τs ∨ σ = .never := by
  constructor
  · intro h
    cases h with
    | refl => exact .inl rfl
    | never => exact .inr rfl
  · rintro (rfl | rfl)
    · exact .refl _
    · exact .never _

/-- A list type fits only itself: a list of pure functions is not a list of
functions with a larger row (effects.function-values). -/
theorem list_iff {σ τ : Ty} : Fits σ (.list τ) ↔ σ = .list τ ∨ σ = .never := by
  constructor
  · intro h
    cases h with
    | refl => exact .inl rfl
    | never => exact .inr rfl
  · rintro (rfl | rfl)
    · exact .refl _
    · exact .never _

/-- A function value fits a function type when the types differ only in a row
that grows (effects.function-values). -/
theorem fn_iff {params params' : List (Mode × Ty)} {result result' : Ty}
    {a b : Row} :
    Fits (.fn params result a) (.fn params' result' b) ↔
      params = params' ∧ result = result' ∧ a.Within b := by
  constructor
  · intro h
    cases h with
    | refl => exact ⟨rfl, rfl, Row.Within.refl _⟩
    | fn h => exact ⟨rfl, rfl, h⟩
  · rintro ⟨rfl, rfl, h⟩
    exact .fn h

end Fits

/-- Instantiating a row's variables keeps its own `resume`. -/
theorem Row.substRows_resume (s : RowSubst) (ρ : Row) : (ρ.substRows s).resume = ρ.resume := by
  cases ρ; rfl

/-- The empty instantiation leaves every row the one `raise` label it has. -/
theorem Ty.instantiableBy_nil (τ : Ty) : τ.InstantiableBy [] := by
  intro ρ _
  refine ⟨fun E hE F hF => ?_, fun _ _ _ h => nomatch h⟩
  cases h : ρ.raise <;> simp_all [Row.labels]

/-- A closed type that names no type parameter, and whose views are viewable, is well
formed in every scope. -/
theorem Ty.Closed.wellFormed {τ : Ty} (h : τ.Closed) (hp : τ.params = [])
    (he : ∀ ρ ∈ τ.rows, ρ.ParamFree) (hv : τ.ViewsViewable) (scope : RowScope) :
    τ.WellFormed scope := by
  refine ⟨fun ρ hρ v hv => ?_, fun T hT => ?_, he, hv⟩
  · rw [h ρ hρ] at hv
    exact nomatch hv
  · rw [hp] at hT
    exact nomatch hT

/-- A type well formed in a scope is well formed in a larger one. -/
theorem Ty.WellFormed.of_le {τ : Ty} {s s' : RowScope} (hs : s.Le s')
    (h : τ.WellFormed s) : τ.WellFormed s' := by
  refine ⟨fun ρ hρ v hv => hs.vars v (h.1 ρ hρ v hv), fun T hT => ?_, h.2.2⟩
  obtain ⟨p, hp, rfl⟩ := List.mem_map.1 (h.2.1 T hT)
  exact List.mem_map_of_mem (hs.types p hp)

end Stilt
