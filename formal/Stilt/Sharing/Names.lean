import Stilt.Modes.Tabled
import Stilt.Modes.Facts

/-!
# The bindings the inference calls shared

The names of a program's bindings whose modifications the inference of modes.shared-writes
calls shared: in each body, a function's, `main`'s or a closure literal's, the bindings that
`ModeEnv.bodyShared` gives, as the facts of `Stilt.Modes.Facts` read each body once
(modes.bindings-and-axes).

The inference reads a binding by its name, from the start of the body that makes it. So it is
the binding's own only in a program that binds each name once, as the reference interpreter's
export gives its programs (`Program.binders`); in a program that binds a name twice, every
binding is shared, and every write copies first.
-/

namespace Stilt

/-- The names an expression binds: by a `let`, a `var`, a `for`, a `catch`, a `when`, a `match`
arm and a closure literal's parameters, closure literals' bodies among them. -/
def Expr.binders (e : Expr) : List Name :=
  e.gather (fun _ _ _ => ()) (fun _ e => match e with
    | .letIn y .. | .varIn y .. | .for y .. | .tryCatch _ _ y .. => [y]
    | .held ns _ _ => ns.map Prod.fst
    | .match _ _ arms => arms.flatMap (·.binders)
    | .closure ps .. => ps.map (·.name)
    | _ => []) ()

/-- The names a program binds: its functions' parameters, and what its bodies bind. -/
def Program.binders (p : Program) : List Name :=
  p.decls.fns.flatMap (fun d => d.params.map (·.name) ++ d.body.binders) ++ p.main.binders

namespace ModeEnv

variable (M : ModeEnv)

/-- The bindings of a body with parameters `ps` that the inference calls shared, and those of
the closure literals in it, each a body of its own, which reads the variables it captures of the
bindings around it (expressions.capture) as parameters. -/
def allShared (ps : List Param) (body : Expr) : List Name :=
  let outer := ps.map (·.name) ++ body.binders
  M.bodyShared ps body ++ body.gather (fun _ _ _ => ()) (fun _ e => match e with
    | .closure qs _ _ b => M.bodyShared qs b (outer.filter (Expr.captures qs b))
    | _ => []) ()

end ModeEnv

/-- The names of the bindings of a program that the inference calls shared, from the program's
rounds kept in tables (`Program.modeEnvTabled`), when the program binds each name once
(modes.shared-writes); every name it binds otherwise. -/
def Program.sharedNames (p : Program) : List Name :=
  if p.binders.Nodup then
    let M := p.modeEnvTabled
    p.decls.fns.flatMap (fun d => M.allShared d.params d.body) ++ M.allShared [] p.main
  else p.binders

/-- They are the names of the bindings whose facts say they are shared, in a program that binds
each name once. -/
theorem Program.sharedNames_eq (p : Program) (h : p.binders.Nodup) :
    p.sharedNames = p.decls.fns.flatMap (fun d => p.modeEnv.allShared d.params d.body) ++
      p.modeEnv.allShared [] p.main := by
  simp only [Program.sharedNames, h, ↓reduceIte, Program.modeEnvTabled_eq]

/-- Whether the inference calls a binding of this name shared: one of `sharedNames` in a program
that binds each name once, and every binding in a program that binds a name twice. -/
def Program.isShared (p : Program) : Name → Bool :=
  if p.binders.Nodup then p.sharedNames.contains else fun _ => true

theorem Program.isShared_of_nodup (p : Program) (h : p.binders.Nodup) :
    p.isShared = p.sharedNames.contains := by
  simp only [Program.isShared, h, ↓reduceIte]

/-- In a program that binds a name twice, every binding is shared. -/
theorem Program.isShared_of_not_nodup (p : Program) (h : ¬p.binders.Nodup) (x : Name) :
    p.isShared x = true := by
  simp only [Program.isShared, h, ↓reduceIte]

end Stilt
