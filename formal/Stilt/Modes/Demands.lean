import Stilt.Modes.Threads
import Stilt.Modes.Traverse

/-!
# Demands

A feature that needs a value's mode states a demand: the least point on an axis that a use
accepts, checked where the use is written, against the mode the rules give, after type checking
(modes.demands). Of the demands of the Reference, the calculus writes two uses, whose values must
be `portable` (shared.tasks-and-modes, E0432): `Shared.new(v)`, and a task's function, given to
`task.spawn` or to `s.spawn` (`Stilt.Typing.Tasks`). A value is `fixed` when its type holds a
view, or when it is a closure literal, or a binding of one, that captures a binding that is
`fixed` (`Stilt.Modes.Threads`).

The demands of `std.par`'s functions, which ask for `calm` and `portable` closures (E0431), are
`Program.ParDemands`' (`Stilt.Modes.ParDemands`). No promise reads the demand: the calculus runs
one task at a time, so a value that one task reaches at the time another does has nothing to be
stated on.
-/

namespace Stilt

/-- The uses of an expression that break a demand, in the scope `scope` of what portability
knows of the bindings in it: each `Shared.new` whose value is `fixed`, and each task's function
that is, given to `task.spawn` or to `s.spawn`, by its point where the model can tell it, and
otherwise by the type of the cell or of the function. -/
def demandVisit (D : Decls) (scope : AxisScope) : Expr → List Unit
  | .op (.world (.sharedNew u)) [e] =>
    if (e.axisOf? D.fixedTy scope).getD (D.fixedTy u) then [()] else []
  | .form .spawn (.letIn _ τ f _) | .form .scopeSpawn (.letIn _ _ _ (.letIn _ τ f _)) =>
    if (f.axisOf? D.fixedTy scope).getD (D.fixedTy τ) then [()] else []
  | _ => []

/-- Whether a body with parameters `ps` keeps every demand it writes (modes.demands): no value
that `Shared.new` takes, and no task's function, is `fixed` (shared.tasks-and-modes, E0432). -/
def Expr.demandsMet (D : Decls) (ps : List Param) (body : Expr) : Bool :=
  (body.gather (axisChild D.fixedTy) (demandVisit D) (ps.map fun p => (p.name, D.fixedTy p.type))).isEmpty

/-- E0432 on the calculus (modes.demands and shared.tasks-and-modes): every function's body and
`main`'s keep the demands they write, so no value placed in a `Shared<T>`, and no task's
function, is `fixed`. -/
def Program.Demands (p : Program) : Prop :=
  (∀ d ∈ p.decls.fns, d.body.demandsMet p.decls d.params = true) ∧ p.main.demandsMet p.decls [] = true

instance (p : Program) : Decidable p.Demands := by
  unfold Program.Demands; exact inferInstance

end Stilt
