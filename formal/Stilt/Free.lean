import Stilt.Syntax

/-!
# The variables an expression uses

A closure captures the variables it uses, by copy, when it is created
(expressions.capture): the variables its body reads, writes or passes that no
binder of the body and no parameter of the closure binds. `Expr.free x e` says
whether `e` uses the variable `x` that a scope around it binds: a binder of `e`
of the name `x` hides it in the binder's scope, as in typing (expressions.shadowing).
-/

namespace Stilt

mutual

/-- Whether `e` uses the variable `x` of a scope around it. -/
def Expr.free (x : Name) : Expr → Bool
  | .var y | .move y => y == x
  | .int _ | .bool _ | .unit | .break | .continue | .fnRef .. | .method .. => false
  | .record _ fields => fieldsFree x fields
  | .variant _ _ es | .list _ es | .op _ es | .view es => exprsFree x es
  | .field e _ | .raise e | .try e | .return e | .loop e | .perform _ e => e.free x
  | .index a b | .seq a b | .while a b | .withH _ _ a b => a.free x || b.free x
  | .closure ps _ _ body => !(ps.any (·.name == x)) && body.free x
  | .call callee args _ => callee.free x || argsFree x args
  | .letIn y _ init body | .varIn y _ init body => init.free x || (y != x && body.free x)
  | .assign ⟨root, path⟩ value => root == x || pathFree x path || value.free x
  | .if c _ a b => c.free x || a.free x || b.free x
  | .match e _ arms => e.free x || armsFree x arms
  | .for y _ it body => it.free x || (y != x && body.free x)
  | .tryCatch e _ y h _ => e.free x || (y != x && h.free x)
  | .held ns hs body => exprsFree x hs || (!(ns.any (·.1 == x)) && body.free x)

/-- Whether an expression of the list uses `x`. -/
def exprsFree (x : Name) : List Expr → Bool
  | [] => false
  | e :: es => e.free x || exprsFree x es

/-- Whether a field of a record literal uses `x`. -/
def fieldsFree (x : Name) : List (Name × Expr) → Bool
  | [] => false
  | (_, e) :: fields => e.free x || fieldsFree x fields

/-- Whether an argument uses `x`: a value that uses it, or a place rooted in it
or whose indexes use it. -/
def argsFree (x : Name) : List Arg → Bool
  | [] => false
  | .value e :: args => e.free x || argsFree x args
  | .inout ⟨root, path⟩ :: args => root == x || pathFree x path || argsFree x args

/-- Whether an index of a place uses `x`. -/
def pathFree (x : Name) : List Projection → Bool
  | [] => false
  | .field _ :: path => pathFree x path
  | .index i :: path => i.free x || pathFree x path

/-- Whether an arm uses `x`, which its binders hide. -/
def armsFree (x : Name) : List Arm → Bool
  | [] => false
  | ⟨_, binders, body⟩ :: arms => (!binders.contains x && body.free x) || armsFree x arms

end

/-- Whether a closure literal with parameters `ps` and body `body` captures `x`:
its body uses `x`, which none of its parameters is (expressions.capture). -/
def Expr.captures (ps : List Param) (body : Expr) (x : Name) : Bool :=
  !(ps.any (·.name == x)) && body.free x

/-- What a closure literal keeps of the variables in scope, the newest first: those
it captures (expressions.capture). -/
def captureOf {α : Type} (ps : List Param) (body : Expr) (scope : List (Name × α)) :
    List (Name × α) :=
  scope.filter fun p => Expr.captures ps body p.1

theorem Expr.free_closure (x : Name) (ps : List Param) (result : Ty) (ρ : Row) (body : Expr) :
    (Expr.closure ps result ρ body).free x = Expr.captures ps body x := by
  simp [Expr.free, Expr.captures]

/-- Keeping the captured variables commutes with any map that keeps names. -/
theorem captureOf_map {α β : Type} (ps : List Param) (body : Expr) (f : α → β) :
    ∀ scope : List (Name × α),
      captureOf ps body (scope.map fun p => (p.1, f p.2)) =
        (captureOf ps body scope).map fun p => (p.1, f p.2) := by
  intro scope
  simp [captureOf, List.filter_map, Function.comp_def]

/-- A variable a closure captures is one of those in scope. -/
theorem mem_of_mem_captureOf {α : Type} {ps : List Param} {body : Expr}
    {scope : List (Name × α)} {p : Name × α} (h : p ∈ captureOf ps body scope) : p ∈ scope :=
  (List.mem_filter.1 h).1

/-- What holds of every variable in scope holds of every captured one. -/
theorem captureOf_forall {α : Type} {ps : List Param} {body : Expr} {scope : List (Name × α)}
    {P : Name × α → Prop} (h : ∀ p ∈ scope, P p) : ∀ p ∈ captureOf ps body scope, P p :=
  fun p hp => h p (mem_of_mem_captureOf hp)

end Stilt
