import Stilt.Modes.Threads
import Stilt.Modes.Traverse

/-!
# The demands of `std.par`

par.what-runs-in-parallel: a function given to `par.map`, `par.each`, `par.both` or `par.fold`
must be `calm` and `portable` (modes.demands), else it is a closure that can't run in parallel,
E0431. The calculus writes each call as a form whose code binds the functions first
(`Stilt.Typing.Par`), so the check reads each function where its form binds it, by its points
on the two thread axes (`Stilt.Modes.Threads`): `fixed` when its type holds a view or it is a
closure literal, or a binding of one, that captures a `fixed` binding, and `contended` when its
type holds a `Shared<T>` or it captures a `contended` binding.

The rows of the functions are empty (`TaskForm`), so they perform nothing; the check adds that
they reach no view and no shared value. No promise reads it: the calculus runs one call at a
time, as `parallel_eq_sequential` runs them, each from copies, so a value that two calls reach at
once has nothing to be stated on. The note of the diagnostic is left out.
-/

namespace Stilt

/-- The functions a form of `std.par` takes, each with the type its code binds it at: `map`'s
and `each`'s function, `both`'s two and `fold`'s. -/
def Expr.parFns : Expr → List (Ty × Expr)
  | .form .parMap (.letIn _ _ _ (.letIn _ τ f _)) | .form .parEach (.letIn _ τ f _)
  | .form .parFold (.letIn _ _ _ (.letIn _ _ _ (.letIn _ τ f _))) => [(τ, f)]
  | .form .parBoth (.letIn _ τ f (.letIn _ σ g _)) => [(τ, f), (σ, g)]
  | _ => []

/-- The functions given to `std.par` that are at the greatest point of the axis `has`, in the
scope `scope` of what the axis knows of the bindings in it: by their points where the model can
tell them, and otherwise by their types. -/
def parVisit (has : Ty → Bool) (scope : AxisScope) (e : Expr) : List Unit :=
  e.parFns.filterMap fun (τ, f) => if (f.axisOf? has scope).getD (has τ) then some () else none

/-- Whether a body with parameters `ps` gives `std.par` no function at the greatest point of the
axis `has`. -/
def Expr.parAxisMet (has : Ty → Bool) (ps : List Param) (body : Expr) : Bool :=
  (body.gather (axisChild has) (parVisit has) (ps.map fun p => (p.name, has p.type))).isEmpty

/-- Whether a body with parameters `ps` gives `std.par` only `portable` and `calm` functions
(par.what-runs-in-parallel, E0431). -/
def Expr.parDemandsMet (D : Decls) (ps : List Param) (body : Expr) : Bool :=
  body.parAxisMet D.fixedTy ps && body.parAxisMet D.contended ps

/-- E0431 on the calculus (par.what-runs-in-parallel and modes.demands): every function's body
and `main`'s give `par.map`, `par.each`, `par.both` and `par.fold` only functions that are
`portable`, reaching no view, and `calm`, reaching no `Shared<T>`, by their types and their
captures. -/
def Program.ParDemands (p : Program) : Prop :=
  (∀ d ∈ p.decls.fns, d.body.parDemandsMet p.decls d.params = true) ∧
    p.main.parDemandsMet p.decls [] = true

instance (p : Program) : Decidable p.ParDemands := by
  unfold Program.ParDemands; exact inferInstance

end Stilt
