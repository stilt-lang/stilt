import Stilt.Generics

/-!
# Instances of instances, and of expressions

Ground types hold no row variable, so instantiating type parameters and row
variables commutes, and an instance of an instance is one instantiation of the
parameters that the first names. An expression is instantiated through every
type it writes; a call of a generic function instantiates its body this way
(types.no-type-arguments).
-/

namespace Stilt

/-! ## Instantiations of rows and of types commute -/

mutual

/-- A closed type has no row variable for an instantiation to replace. -/
theorem Ty.substRows_of_closed (θ : RowSubst) : ∀ τ : Ty, τ.Closed → τ.substRows θ = τ
  | .int _, _ | .float _, _ | .bool, _ | .str, _ | .unit, _ | .never, _ => rfl
  | .record _, _ | .variant _, _ | .param _, _ => rfl
  | .list τ, h => by
    rw [Ty.substRows, Ty.substRows_of_closed θ τ fun ρ hρ => h ρ (by simpa [Ty.rows] using hρ)]
  | .tuple τs, h => by
    rw [Ty.substRows, substTysRows_of_closed θ τs fun ρ hρ => h ρ (by simpa [Ty.rows] using hρ)]
  | .map κ τ, h => by
    rw [Ty.substRows, Ty.substRows_of_closed θ κ fun σ hσ => h σ (by simp [Ty.rows, hσ]),
      Ty.substRows_of_closed θ τ fun σ hσ => h σ (by simp [Ty.rows, hσ])]
  | .set τ, h => by
    rw [Ty.substRows, Ty.substRows_of_closed θ τ fun ρ hρ => h ρ (by simpa [Ty.rows] using hρ)]
  | .view τ, h => by
    rw [Ty.substRows, Ty.substRows_of_closed θ τ fun ρ hρ => h ρ (by simpa [Ty.rows] using hρ)]
  | .shared τ, h => by
    rw [Ty.substRows, Ty.substRows_of_closed θ τ fun ρ hρ => h ρ (by simpa [Ty.rows] using hρ)]
  | .fn ps r ρ, h => by
    rw [Ty.substRows, substParamRows_of_closed θ ps fun σ hσ => h σ (by simp [Ty.rows, hσ]),
      Ty.substRows_of_closed θ r fun σ hσ => h σ (by simp [Ty.rows, hσ]),
      Row.substRows_of_closed θ ρ fun σ hσ => h σ (by simp [Ty.rows, hσ])]

theorem substTysRows_of_closed (θ : RowSubst) :
    ∀ τs : List Ty, (∀ ρ ∈ tysRows τs, ρ.vars = []) → substTysRows θ τs = τs
  | [], _ => rfl
  | τ :: τs, h => by
    rw [substTysRows, Ty.substRows_of_closed θ τ fun ρ hρ => h ρ (by simp [tysRows, hρ]),
      substTysRows_of_closed θ τs fun ρ hρ => h ρ (by simp [tysRows, hρ])]

theorem substParamRows_of_closed (θ : RowSubst) :
    ∀ ps : List (Mode × Ty), (∀ ρ ∈ paramRows ps, ρ.vars = []) → substParamRows θ ps = ps
  | [], _ => rfl
  | (m, τ) :: ps, h => by
    rw [substParamRows, Ty.substRows_of_closed θ τ fun ρ hρ => h ρ (by simp [paramRows, hρ]),
      substParamRows_of_closed θ ps fun ρ hρ => h ρ (by simp [paramRows, hρ])]

theorem Row.substRows_of_closed (θ : RowSubst) :
    ∀ ρ : Row, (∀ σ ∈ ρ.rows, σ.vars = []) → ρ.substRows θ = ρ
  | ⟨io, some E, vs, es, r⟩, h => by
    have hvs : vs = [] := h ⟨io, some E, vs, es, r⟩ (by simp [Row.rows])
    subst hvs
    simp [Row.substRows, Ty.substRows_of_closed θ E fun σ hσ => h σ (by simp [Row.rows, hσ])]
  | ⟨io, none, vs, es, r⟩, h => by
    have hvs : vs = [] := h ⟨io, none, vs, es, r⟩ (by simp [Row.rows])
    subst hvs
    simp [Row.substRows]

end

mutual

/-- Ground types have no row variables, so instantiating type parameters and
row variables in either order gives the same type. -/
theorem Ty.substTys_substRows {s : TySubst} (hs : s.Ground) (θ : RowSubst) :
    ∀ τ : Ty, (τ.substTys s).substRows θ = (τ.substRows θ).substTys s
  | .int _ | .float _ | .bool | .str | .unit | .never | .record _ | .variant _ => rfl
  | .param T => by
    cases hl : s.lookup T with
    | none => simp [Ty.substTys, Ty.substRows, hl]
    | some σ =>
      simp [Ty.substTys, Ty.substRows, hl, Ty.substRows_of_closed θ σ (hs _ (mem_of_lookup hl)).1]
  | .list τ => by rw [Ty.substTys, Ty.substRows, Ty.substRows, Ty.substTys, Ty.substTys_substRows hs θ τ]
  | .tuple τs => by
    rw [Ty.substTys, Ty.substRows, Ty.substRows, Ty.substTys, substTyList_substRows hs θ τs]
  | .map κ τ => by
    rw [Ty.substTys, Ty.substRows, Ty.substRows, Ty.substTys, Ty.substTys_substRows hs θ κ,
      Ty.substTys_substRows hs θ τ]
  | .set τ => by rw [Ty.substTys, Ty.substRows, Ty.substRows, Ty.substTys, Ty.substTys_substRows hs θ τ]
  | .view τ => by rw [Ty.substTys, Ty.substRows, Ty.substRows, Ty.substTys, Ty.substTys_substRows hs θ τ]
  | .shared τ => by rw [Ty.substTys, Ty.substRows, Ty.substRows, Ty.substTys, Ty.substTys_substRows hs θ τ]
  | .fn ps r ρ => by
    rw [Ty.substTys, Ty.substRows, Ty.substRows, Ty.substTys, substParamTys_substRows hs θ ps,
      Ty.substTys_substRows hs θ r]

theorem substTyList_substRows {s : TySubst} (hs : s.Ground) (θ : RowSubst) :
    ∀ τs : List Ty, substTysRows θ (substTyList s τs) = substTyList s (substTysRows θ τs)
  | [] => rfl
  | τ :: τs => by
    rw [substTyList, substTysRows, substTysRows, substTyList, Ty.substTys_substRows hs θ τ,
      substTyList_substRows hs θ τs]

theorem substParamTys_substRows {s : TySubst} (hs : s.Ground) (θ : RowSubst) :
    ∀ ps : List (Mode × Ty), substParamRows θ (substParamTys s ps) = substParamTys s (substParamRows θ ps)
  | [] => rfl
  | (m, τ) :: ps => by
    rw [substParamTys, substParamRows, substParamRows, substParamTys, Ty.substTys_substRows hs θ τ,
      substParamTys_substRows hs θ ps]

end

/-! ## An instance of an instance -/

/-- The instantiation `s` followed by `s'`, as one instantiation of the
parameters that `s` names. -/
def TySubst.then (s s' : TySubst) : TySubst := s.map (Prod.map id (Ty.substTys s'))

mutual

/-- Instantiating a type's parameters with `s`, and the parameters of the
result with `s'`, is one instantiation, when `s` names all of the type's. -/
theorem Ty.substTys_substTys (s s' : TySubst) :
    ∀ τ : Ty, (∀ T ∈ τ.params, (s.lookup T).isSome) →
      (τ.substTys s).substTys s' = τ.substTys (s.then s')
  | .int _, _ | .float _, _ | .bool, _ | .str, _ | .unit, _ | .never, _ => rfl
  | .record _, _ | .variant _, _ => rfl
  | .param T, h => by
    obtain ⟨σ, hl⟩ := Option.isSome_iff_exists.1 (h T (by simp [Ty.params]))
    simp [Ty.substTys, TySubst.then, hl, lookup_map_snd]
  | .list τ, h => by rw [Ty.substTys, Ty.substTys, Ty.substTys, Ty.substTys_substTys s s' τ h]
  | .tuple τs, h => by
    rw [Ty.substTys, Ty.substTys, Ty.substTys, substTyList_substTys s s' τs h]
  | .map κ τ, h => by
    rw [Ty.substTys, Ty.substTys, Ty.substTys,
      Ty.substTys_substTys s s' κ fun T hT => h T (by simp [Ty.params, hT]),
      Ty.substTys_substTys s s' τ fun T hT => h T (by simp [Ty.params, hT])]
  | .set τ, h => by rw [Ty.substTys, Ty.substTys, Ty.substTys, Ty.substTys_substTys s s' τ h]
  | .view τ, h => by rw [Ty.substTys, Ty.substTys, Ty.substTys, Ty.substTys_substTys s s' τ h]
  | .shared τ, h => by rw [Ty.substTys, Ty.substTys, Ty.substTys, Ty.substTys_substTys s s' τ h]
  | .fn ps r _, h => by
    rw [Ty.substTys, Ty.substTys, Ty.substTys,
      substParamTys_substTys s s' ps fun T hT => h T (by simp [Ty.params, hT]),
      Ty.substTys_substTys s s' r fun T hT => h T (by simp [Ty.params, hT])]

theorem substTyList_substTys (s s' : TySubst) :
    ∀ τs : List Ty, (∀ T ∈ tysParams τs, (s.lookup T).isSome) →
      substTyList s' (substTyList s τs) = substTyList (s.then s') τs
  | [], _ => rfl
  | τ :: τs, h => by
    rw [substTyList, substTyList, substTyList,
      Ty.substTys_substTys s s' τ fun T hT => h T (by simp [tysParams, hT]),
      substTyList_substTys s s' τs fun T hT => h T (by simp [tysParams, hT])]

theorem substParamTys_substTys (s s' : TySubst) :
    ∀ ps : List (Mode × Ty), (∀ T ∈ paramTysParams ps, (s.lookup T).isSome) →
      substParamTys s' (substParamTys s ps) = substParamTys (s.then s') ps
  | [], _ => rfl
  | (m, τ) :: ps, h => by
    rw [substParamTys, substParamTys, substParamTys,
      Ty.substTys_substTys s s' τ fun T hT => h T (by simp [paramTysParams, hT]),
      substParamTys_substTys s s' ps fun T hT => h T (by simp [paramTysParams, hT])]

end

/-- `zip` of names with types, followed by `s'`, zips the names with the
types' instances. -/
theorem TySubst.then_zip (names : List Name) (τs : List Ty) (s' : TySubst) :
    TySubst.then (names.zip τs) s' = names.zip (τs.map (Ty.substTys s')) := by
  simp [TySubst.then, List.zip_map_right]

/-! ## Expressions -/

/-- Replaces the type parameters in the type an operation on the world names, the type of
the cell that `Shared.new` makes (shared.std-sync). No other one names a type. -/
def WorldOp.substTys (s : TySubst) : WorldOp → WorldOp
  | .sharedNew u => .sharedNew (u.substTys s)
  | k => k

/-- Replaces the type parameters in the type an operation names. -/
def Op.substTys (s : TySubst) : Op → Op
  | .world k => .world (k.substTys s)
  | o => o

@[simp] theorem Op.substTys_world (s : TySubst) (k : WorldOp) :
    (Op.world k).substTys s = .world (k.substTys s) := rfl

@[simp] theorem Op.substTys_of_ne {s : TySubst} {o : Op} (h : ∀ k, o ≠ .world k) : o.substTys s = o := by
  cases o <;> first | rfl | exact absurd rfl (h _)

/-- What reads every operation on the world alike reads an operation alike once its type
parameters are replaced. -/
theorem Op.substTys_congr {β : Sort _} (f : Op → β) (hf : ∀ k k', f (.world k) = f (.world k'))
    (s : TySubst) (o : Op) : f (o.substTys s) = f o := by
  cases o <;> first | rfl | exact hf _ _

@[simp] theorem Op.substTys_nil (o : Op) : o.substTys [] = o := by
  cases o <;> try rfl
  rename_i k
  cases k <;> simp [WorldOp.substTys, Ty.substTys_nil]

mutual

/-- Replaces the type parameters in every type an expression writes. A call
of a generic function applies its instantiation to the function's body, as
the elaborated program instantiates a generic function at each use
(types.no-type-arguments). Only functions declare type parameters, so nothing inside a
body binds one. -/
def Expr.substTys (s : TySubst) : Expr → Expr
  | .var x => .var x
  | .move x => .move x
  | .int n => .int n
  | .bool b => .bool b
  | .unit => .unit
  | .record R fields => .record R (substFieldTys s fields)
  | .variant T C es => .variant T C (substExprTys s es)
  | .list τ es => .list (τ.substTys s) (substExprTys s es)
  | .op o es => .op (o.substTys s) (substExprTys s es)
  | .view es => .view (substExprTys s es)
  | .field e f => .field (e.substTys s) f
  | .index e i => .index (e.substTys s) (i.substTys s)
  | .fnRef f tys rows => .fnRef f (substTyList s tys) rows
  | .method t m τ => .method t m (τ.substTys s)
  | .closure ps r ρ body => .closure (ps.map (Param.substTys s)) (r.substTys s) ρ (body.substTys s)
  | .call f args τ => .call (f.substTys s) (substArgTys s args) (τ.substTys s)
  | .letIn x τ e body => .letIn x (τ.substTys s) (e.substTys s) (body.substTys s)
  | .varIn x τ e body => .varIn x (τ.substTys s) (e.substTys s) (body.substTys s)
  | .assign ⟨x, path⟩ e => .assign ⟨x, substPathTys s path⟩ (e.substTys s)
  | .seq a b => .seq (a.substTys s) (b.substTys s)
  | .if c τ a b => .if (c.substTys s) (τ.substTys s) (a.substTys s) (b.substTys s)
  | .match e τ arms => .match (e.substTys s) (τ.substTys s) (substArmTys s arms)
  | .for x τ e body => .for x (τ.substTys s) (e.substTys s) (body.substTys s)
  | .raise e => .raise (e.substTys s)
  | .try e => .try (e.substTys s)
  | .tryCatch e E x h τ =>
    .tryCatch (e.substTys s) (E.substTys s) x (h.substTys s) (τ.substTys s)
  | .while c body => .while (c.substTys s) (body.substTys s)
  | .loop body => .loop (body.substTys s)
  | .break => .break
  | .continue => .continue
  | .return e => .return (e.substTys s)
  | .perform op e => .perform op (e.substTys s)
  | .withH E c h b => .withH E c (h.substTys s) (b.substTys s)
  | .held ns hs body =>
    .held (ns.map fun p => (p.1, p.2.substTys s)) (substExprTys s hs) (body.substTys s)

/-- Replaces the type parameters in a list of expressions. -/
def substExprTys (s : TySubst) : List Expr → List Expr
  | [] => []
  | e :: es => e.substTys s :: substExprTys s es

/-- Replaces the type parameters in the fields of a record literal. -/
def substFieldTys (s : TySubst) : List (Name × Expr) → List (Name × Expr)
  | [] => []
  | (f, e) :: fields => (f, e.substTys s) :: substFieldTys s fields

/-- Replaces the type parameters in the arguments of a call. -/
def substArgTys (s : TySubst) : List Arg → List Arg
  | [] => []
  | .value e :: args => .value (e.substTys s) :: substArgTys s args
  | .inout ⟨x, path⟩ :: args => .inout ⟨x, substPathTys s path⟩ :: substArgTys s args

/-- Replaces the type parameters in the indexes of a place. -/
def substPathTys (s : TySubst) : List Projection → List Projection
  | [] => []
  | .field f :: path => .field f :: substPathTys s path
  | .index i :: path => .index (i.substTys s) :: substPathTys s path

/-- Replaces the type parameters in the arms of a `match`. -/
def substArmTys (s : TySubst) : List Arm → List Arm
  | [] => []
  | ⟨C, binders, body⟩ :: arms => ⟨C, binders, body.substTys s⟩ :: substArmTys s arms

end

mutual

theorem Expr.substTys_nil : ∀ e : Expr, e.substTys [] = e
  | .var _ | .move _ | .int _ | .bool _ | .unit => rfl
  | .record _ fields => by rw [Expr.substTys, substFieldTys_nil fields]
  | .variant _ _ es => by rw [Expr.substTys, substExprTys_nil es]
  | .list τ es => by rw [Expr.substTys, Ty.substTys_nil τ, substExprTys_nil es]
  | .op o es => by rw [Expr.substTys, substExprTys_nil es, Op.substTys_nil]
  | .view es => by rw [Expr.substTys, substExprTys_nil es]
  | .field e _ => by rw [Expr.substTys, Expr.substTys_nil e]
  | .index e i => by rw [Expr.substTys, Expr.substTys_nil e, Expr.substTys_nil i]
  | .fnRef _ tys _ => by
    rw [Expr.substTys, substTyList_eq_map, show Ty.substTys [] = id from funext Ty.substTys_nil,
      List.map_id]
  | .method _ _ τ => by rw [Expr.substTys, Ty.substTys_nil τ]
  | .closure ps r ρ body => by
    rw [Expr.substTys, show Param.substTys [] = id from funext Param.substTys_nil, List.map_id,
      Ty.substTys_nil r, Expr.substTys_nil body]
  | .call f args _ => by rw [Expr.substTys, Expr.substTys_nil f, substArgTys_nil args, Ty.substTys_nil]
  | .letIn _ τ e body => by
    rw [Expr.substTys, Ty.substTys_nil τ, Expr.substTys_nil e, Expr.substTys_nil body]
  | .varIn _ τ e body => by
    rw [Expr.substTys, Ty.substTys_nil τ, Expr.substTys_nil e, Expr.substTys_nil body]
  | .assign ⟨_, path⟩ e => by rw [Expr.substTys, substPathTys_nil path, Expr.substTys_nil e]
  | .seq a b => by rw [Expr.substTys, Expr.substTys_nil a, Expr.substTys_nil b]
  | .if c τ a b => by
    rw [Expr.substTys, Expr.substTys_nil c, Ty.substTys_nil τ, Expr.substTys_nil a,
      Expr.substTys_nil b]
  | .match e τ arms => by
    rw [Expr.substTys, Expr.substTys_nil e, Ty.substTys_nil τ, substArmTys_nil arms]
  | .for _ τ e body => by
    rw [Expr.substTys, Ty.substTys_nil τ, Expr.substTys_nil e, Expr.substTys_nil body]
  | .raise e => by rw [Expr.substTys, Expr.substTys_nil e]
  | .try e => by rw [Expr.substTys, Expr.substTys_nil e]
  | .tryCatch e E _ h τ => by
    rw [Expr.substTys, Expr.substTys_nil e, Ty.substTys_nil E, Expr.substTys_nil h,
      Ty.substTys_nil τ]
  | .while c body => by rw [Expr.substTys, Expr.substTys_nil c, Expr.substTys_nil body]
  | .loop body => by rw [Expr.substTys, Expr.substTys_nil body]
  | .break | .continue => rfl
  | .return e => by rw [Expr.substTys, Expr.substTys_nil e]
  | .perform _ e => by rw [Expr.substTys, Expr.substTys_nil e]
  | .withH _ _ h b => by rw [Expr.substTys, Expr.substTys_nil h, Expr.substTys_nil b]
  | .held ns hs body => by
    simp only [Expr.substTys, Ty.substTys_nil, substExprTys_nil hs, Expr.substTys_nil body]
    simp

theorem substExprTys_nil : ∀ es : List Expr, substExprTys [] es = es
  | [] => rfl
  | e :: es => by rw [substExprTys, Expr.substTys_nil e, substExprTys_nil es]

theorem substFieldTys_nil : ∀ fields : List (Name × Expr), substFieldTys [] fields = fields
  | [] => rfl
  | (_, e) :: fields => by rw [substFieldTys, Expr.substTys_nil e, substFieldTys_nil fields]

theorem substArgTys_nil : ∀ args : List Arg, substArgTys [] args = args
  | [] => rfl
  | .value e :: args => by rw [substArgTys, Expr.substTys_nil e, substArgTys_nil args]
  | .inout ⟨_, path⟩ :: args => by
    rw [substArgTys, substPathTys_nil path, substArgTys_nil args]

theorem substPathTys_nil : ∀ path : List Projection, substPathTys [] path = path
  | [] => rfl
  | .field _ :: path => by rw [substPathTys, substPathTys_nil path]
  | .index i :: path => by rw [substPathTys, Expr.substTys_nil i, substPathTys_nil path]

theorem substArmTys_nil : ∀ arms : List Arm, substArmTys [] arms = arms
  | [] => rfl
  | ⟨_, _, body⟩ :: arms => by rw [substArmTys, Expr.substTys_nil body, substArmTys_nil arms]

end

theorem length_substExprTys (s : TySubst) : ∀ es : List Expr, (substExprTys s es).length = es.length
  | [] => rfl
  | _ :: es => by simp [substExprTys, length_substExprTys s es]

end Stilt
