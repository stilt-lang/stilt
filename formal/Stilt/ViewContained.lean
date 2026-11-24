import Stilt.Sources

/-!
# Views that stay inside their sources' scopes

A view never leaves the scope that binds one of its sources (views.escaping,
E0422). The value of a block reads no binding the block makes, the value of an
arm none of its pattern's binders, and the value of a `catch` arm not the error
it binds. An assignment of a view gives it to a variable bound in the body, with a written
type, after each of its sources: a parameter, a captured variable and a pattern's
binder are given no view. A function's result, and the value of each `return` and
`raise` that leaves it, reads only its parameters (views.across-calls), and so does
a closure literal's, whose captured views are the literal's own sources
(views.fixed).
-/

namespace Stilt

/-- Whether `y` is bound in `Γ` no later than `x`: its scope holds `x`'s. -/
def ViewScope.outlives (Γ : ViewScope) (y x : Name) : Bool :=
  match Γ.findIdx? (·.1 == x), Γ.findIdx? (·.1 == y) with
  | some i, some j => i ≤ j
  | _, _ => false

/-- Whether a value that reads `sources` may leave a body that gives it, whose
`let` parameters of a viewable type or a view type are `params`: it reads them
alone, each whole (views.across-calls). A view of a part of a parameter reads
the callee's copy, and one of an `inout` parameter is a result that writes,
which E0428 checks (projections.results-that-write). -/
def leaves (params : List Name) (sources : List Shape) : Bool :=
  sources.all fun s => params.contains s.root && s.fields.isEmpty

/-- The parameters that a body's result may view: none when its result type
isn't a view type, else its `let` parameters of a viewable type or a view type
(views.across-calls). -/
def resultParams (D : Decls) (ps : List Param) (result : Ty) : List Name :=
  if result.isView D then
    (ps.filter fun p => p.mode != .inout && p.type.viewSource).map (·.name)
  else []

mutual

/-- Whether no view of `e` outlives a source (views.escaping, E0422), in a body
whose result may read the parameters `params`. -/
def Expr.contained (D : Decls) (Γ : ViewScope) (params : List Name) : Expr → Bool
  | .var _ | .move _ | .int _ | .bool _ | .unit | .break | .continue | .fnRef _ _ _
  | .method _ _ _ => true
  | .record _ fields => fieldsContained D Γ params fields
  | .variant _ _ es | .list _ es | .op _ es | .view es => exprsContained D Γ params es
  | .field e _ | .try e | .perform _ e | .loop e => e.contained D Γ params
  | .raise e | .return e => e.contained D Γ params && leaves params (e.sources D Γ)
  | .index a b | .seq a b | .while a b | .withH _ _ a b =>
    a.contained D Γ params && b.contained D Γ params
  | .closure ps result _ body =>
    let Γ' := Γ.enter D ps
    body.contained D Γ' (resultParams D ps result) &&
      leaves (resultParams D ps result) (body.sources D Γ')
  | .call callee args _ => callee.contained D Γ params && argsContained D Γ params args
  | .held ns hs body =>
    exprsContained D Γ params hs &&
      let Γ' := Γ.holding D ns
      body.contained D Γ' (params.removeAll (ns.map (·.1))) &&
        (body.sources D Γ').all fun s => !(ns.map (·.1)).contains s.root
  | .letIn x τ init body | .varIn x τ init body =>
    init.contained D Γ params &&
      let Γ' := Γ.bind D x τ (init.sources D Γ)
      body.contained D Γ' (params.filter (· != x)) && (body.sources D Γ').all (·.root != x)
  | .assign ⟨root, path⟩ value =>
    pathContained D Γ params path && value.contained D Γ params &&
      (value.sources D Γ).all fun s =>
        s.root != root && Γ.outlives s.root root &&
          (Γ.lookup root).all fun b => !b.param && b.type.isSome
  | .if c _ a b => c.contained D Γ params && a.contained D Γ params && b.contained D Γ params
  | .match e _ arms =>
    e.contained D Γ params && armsContained D Γ params (e.sources D Γ) arms
  | .for x τ e body => e.contained D Γ params && body.contained D (Γ.bind D x τ []) (params.filter (· != x))
  | .tryCatch e E x h _ =>
    e.contained D Γ params &&
      h.contained D (Γ.bind D x E []) (params.filter (· != x)) &&
        (h.sources D (Γ.bind D x E [])).all (·.root != x)

/-- Whether no view of a list's expressions outlives a source. -/
def exprsContained (D : Decls) (Γ : ViewScope) (params : List Name) : List Expr → Bool
  | [] => true
  | e :: es => e.contained D Γ params && exprsContained D Γ params es

/-- Whether no view of a record literal's fields outlives a source. -/
def fieldsContained (D : Decls) (Γ : ViewScope) (params : List Name) :
    List (Name × Expr) → Bool
  | [] => true
  | (_, e) :: fields => e.contained D Γ params && fieldsContained D Γ params fields

/-- Whether no view of a call's arguments outlives a source. -/
def argsContained (D : Decls) (Γ : ViewScope) (params : List Name) : List Arg → Bool
  | [] => true
  | .value e :: args => e.contained D Γ params && argsContained D Γ params args
  | .inout ⟨_, path⟩ :: args => pathContained D Γ params path && argsContained D Γ params args

/-- Whether no view of a place's indexes outlives a source. -/
def pathContained (D : Decls) (Γ : ViewScope) (params : List Name) : List Projection → Bool
  | [] => true
  | .field _ :: path => pathContained D Γ params path
  | .index i :: path => i.contained D Γ params && pathContained D Γ params path

/-- Whether no arm's value reads a binder of its pattern. -/
def armsContained (D : Decls) (Γ : ViewScope) (params : List Name) (scrutinee : List Shape) :
    List Arm → Bool
  | [] => true
  | ⟨_, binders, body⟩ :: arms =>
    let Γ' := Γ.binders binders scrutinee
    body.contained D Γ' (params.filter (!binders.contains ·)) &&
      (body.sources D Γ').all (!binders.contains ·.root) &&
        armsContained D Γ params scrutinee arms

end

/-- No view of the program outlives its source: E0422 rejects nothing in it
(views.escaping). A function's result reads only its parameters, and `main`'s none of
its locals. -/
def Program.ViewsContained (p : Program) : Prop :=
  (∀ d ∈ p.decls.fns,
    let Γ := d.viewScope p.decls
    let params := resultParams p.decls d.params d.result
    d.body.contained p.decls Γ params = true ∧ leaves params (d.body.sources p.decls Γ) = true) ∧
    p.main.contained p.decls [] [] = true

end Stilt
