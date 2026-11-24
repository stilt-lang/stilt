import Stilt.Free
import Stilt.Ops
import Stilt.Places

/-!
# The sources of views

The places a view reads, its **sources** (views.making-view), as the checks of
`Stilt.ViewReads` and `Stilt.ViewContained` follow them through a body. A view
made from a place reads the place; a view made from a view, or `v.view(a, b)`,
reads what that view reads; a view made from any other expression reads a
temporary, which nothing can name or change, so it has no source. A call whose
result type, which the call carries, is a view type or a type parameter gives a view that reads what
its arguments of a viewable type or a view type read, those passed `inout` among
them (views.across-calls), and a closure literal what the views it captures read
(views.fixed).

A binding keeps the sources of its initializer when its type may hold a view: a
view, `Option<V>` for a view type `V`, a function type, whose closure may
capture one, and a type parameter (views.view-types). The analysis is lexical
and syntactic, as the reference interpreter's is: a source is a place's shape,
which `Shape.overlaps` compares as modes.overlap does.
-/

namespace Stilt

/-- What the checks of views know of a binding in scope: its type, unless it
is a pattern's binder, whose type the calculus doesn't write, the places
that the view it holds reads, none if it holds no view, and whether the body
in scope got it from outside: a parameter, or a variable a closure captures. -/
structure ViewBinding where
  type : Option Ty
  sources : List Shape
  param : Bool := false

/-- The bindings in scope, the newest first. -/
abbrev ViewScope := List (Name × ViewBinding)

/-- Whether a written type is a view type: `View<T>`, or `Option<V>` for a view
type `V`, a variant one of whose constructors holds a view (views.view-types).
A function type that a signature writes isn't one, so no function gives a
closure that captures a view (views.escaping). -/
def Ty.isView (D : Decls) : Ty → Bool
  | .view _ => true
  | .variant T => match D.variant? T with
    | some t => t.ctors.any fun c => c.2.any fun | .view _ => true | _ => false
    | none => false
  | _ => false

/-- Whether a value of the type may be a view once its type parameters are
replaced: a view type, or a type parameter (views.view-types). -/
def Ty.mayBeView (D : Decls) : Ty → Bool
  | .param _ => true
  | τ => τ.isView D

/-- Whether a binding of the type may hold a view: a view type, a function
type, whose closure literal may capture one, and a type parameter (views.fixed). -/
def Ty.holdsView (D : Decls) (τ : Ty) : Bool :=
  match τ with
  | .fn .. | .param _ => true
  | _ => τ.isView D

/-- Whether a value of the type is a view or can be viewed: a view of it, or
the view itself, reads it (views.viewable-types and views.across-calls). -/
def Ty.viewSource : Ty → Bool
  | .view _ | .str | .list _ => true
  | _ => false

/-- The type of the part of a value of type `τ` that a path reaches. -/
def Ty.along (D : Decls) : Ty → List Projection → Option Ty
  | τ, [] => some τ
  | .record R, .field f :: path =>
    ((D.record? R).bind fun r => r.fields.lookup f).bind fun τ => Ty.along D τ path
  | .tuple τs, .field f :: path => ((positions τs).lookup f).bind fun τ => Ty.along D τ path
  | .list τ, .index _ :: path => Ty.along D τ path
  | _, _ => none

/-- Binds `x` of type `τ` to a value that reads `sources`, which it keeps when
its type may hold a view. -/
def ViewScope.bind (D : Decls) (Γ : ViewScope) (x : Name) (τ : Ty) (sources : List Shape) : ViewScope :=
  (x, ⟨some τ, if τ.holdsView D then sources else [], false⟩) :: Γ

/-- The scope with the names of a `when` bound, each to the value of a cell, a place of its
own that reads no other (shared.when). -/
def ViewScope.holding (D : Decls) (Γ : ViewScope) (names : List (Name × Ty)) : ViewScope :=
  names.foldl (fun Γ p => Γ.bind D p.1 p.2 []) Γ

/-- The sources a parameter is bound with: its own place, as the caller's argument stands
for it (views.across-calls), unless it has a function type, whose closure the caller made and
which holds no view of the callee's (views.view-types). -/
def Param.viewSources (p : Param) : List Shape :=
  match p.type with
  | .fn .. => []
  | _ => [⟨p.name, []⟩]

/-- Binds a body's parameters, each reading the sources `Param.viewSources` gives it. -/
def ViewScope.params (D : Decls) (Γ : ViewScope) (ps : List Param) : ViewScope :=
  ps.foldl (fun Γ p =>
    (p.name, ⟨some p.type, if p.type.holdsView D then p.viewSources else [], true⟩) :: Γ) Γ

/-- The scope a closure's body starts in: the variables around the literal, which it
captures, and its parameters, each got from outside the body. -/
def ViewScope.enter (D : Decls) (Γ : ViewScope) (ps : List Param) : ViewScope :=
  ViewScope.params D (Γ.map fun xb => (xb.1, { xb.2 with param := true })) ps

/-- The parameters of a function, the scope its body starts in. -/
def FnDecl.viewScope (D : Decls) (d : FnDecl) : ViewScope := ViewScope.params D [] d.params

/-- The sources of a place used as a view's source or as an argument: what the view it
holds reads, when it is of a type that may hold a view, `Option<V>` and function types among
them, or the place, when it is of a viewable type (views.making-view and views.across-calls). A place whose type isn't
known, or is a type parameter, which may be either, has both. -/
def ViewScope.placeSources (D : Decls) (Γ : ViewScope) (p : Place) : List Shape :=
  match Γ.lookup p.root with
  | some ⟨some τ, sources, _⟩ => match τ.along D p.path with
    | some (.param _) | none => p.shape :: sources
    | some σ => if σ.holdsView D then sources else if σ.viewSource then [p.shape] else []
  | some ⟨none, sources, _⟩ => p.shape :: sources
  | none => [p.shape]

/-- The sources of a view's source operand, or of a value argument, given the
sources its value reads: a place's, or a temporary's value's. -/
def ViewScope.operandSources (D : Decls) (Γ : ViewScope) (e : Expr) (value : List Shape) :
    List Shape :=
  match e.place? with
  | some p => Γ.placeSources D p
  | none => value

/-- Binds a pattern's binders, which read what the scrutinee reads: `Some(v)`
binds the view of an `Option<V>`. -/
def ViewScope.binders (Γ : ViewScope) (xs : List Name) (scrutinee : List Shape) : ViewScope :=
  xs.foldl (fun Γ x => (x, ⟨none, scrutinee, false⟩) :: Γ) Γ

mutual

/-- The places that the view a value is, or holds, reads (views.making-view). -/
def Expr.sources (D : Decls) (Γ : ViewScope) : Expr → List Shape
  | .var x | .move x => ((Γ.lookup x).map (·.sources)).getD []
  | .view es => headSources D Γ es
  | .variant _ _ es => exprsSources D Γ es
  | .closure ps _ _ body => (captureOf ps body Γ).flatMap (·.2.sources)
  | .call callee args τ =>
    if τ.mayBeView D then callee.sources D Γ ++ argsSources D Γ args else []
  | .letIn x τ init body | .varIn x τ init body => body.sources D (Γ.bind D x τ (init.sources D Γ))
  | .seq _ b | .try b | .withH _ _ _ b => b.sources D Γ
  | .if _ _ a b => a.sources D Γ ++ b.sources D Γ
  | .match e _ arms => armsSources D Γ (e.sources D Γ) arms
  | .tryCatch e E x h _ => e.sources D Γ ++ h.sources D (Γ.bind D x E [])
  | .held ns _ body => body.sources D (Γ.holding D ns)
  | _ => []

/-- The sources of a view's operands: its source's, a place itself among them whatever its
type, since a view of a place that holds no view reads the place (views.making-view). -/
def headSources (D : Decls) (Γ : ViewScope) : List Expr → List Shape
  | [] => []
  | e :: _ => match e.place? with
    | some p => p.shape :: Γ.placeSources D p
    | none => e.sources D Γ

/-- The sources of a variant's payload, `Some(v)` of a view among them. -/
def exprsSources (D : Decls) (Γ : ViewScope) : List Expr → List Shape
  | [] => []
  | e :: es => e.sources D Γ ++ exprsSources D Γ es

/-- The sources of a call's arguments: of each of a viewable type or a view
type, and of each `inout` place (views.across-calls). -/
def argsSources (D : Decls) (Γ : ViewScope) : List Arg → List Shape
  | [] => []
  | .value e :: args => Γ.operandSources D e (e.sources D Γ) ++ argsSources D Γ args
  | .inout p :: args => Γ.placeSources D p ++ argsSources D Γ args

/-- The sources of the arms' values. -/
def armsSources (D : Decls) (Γ : ViewScope) (scrutinee : List Shape) : List Arm → List Shape
  | [] => []
  | ⟨_, binders, body⟩ :: arms =>
    body.sources D (ViewScope.binders Γ binders scrutinee) ++
      armsSources D Γ scrutinee arms

end

end Stilt
