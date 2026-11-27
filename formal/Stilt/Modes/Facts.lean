import Stilt.Modes.Uniqueness
import Stilt.Modes.Traverse
import Stilt.Modes.Threads

/-!
# The modes of a program's bindings

The five axes as facts of the model's bindings (modes.bindings-and-axes): each `let`
and `var` binding, each parameter, and each closure literal, which a `let` or
`var` that binds it names (modes.show). They are inferred by modes.bindings-and-axes from
the elaborated program, and nothing in typing reads them (modes.fact-not-type).

A body is read once, with a context (`ModeCtx`) that flows from each
expression to its parts: the part of its value that leaves the function, as
`Expr.leaves` follows it (modes.escaping and modes.not-escaping); whether it is a closure literal
that runs once (modes.once-closures) or that a binding names; and which variables in scope
may give their storage up at a last use. Those are read from the modes of each binding
(`bindingModes`, `paramModes`, `closureModes`), as `Stilt.Modes.Lattice` reads a point: a binding
whose modes are `local` and `unique` (`Modes.reuses`), or a capture of a closure literal whose
modes are `once`, which its body owns (`Modes.runsOnce`, modes.once-closures and
modes.once-parameters). `Stilt.Modes.Agreement` reads the last of these, so the modes on
locality, uniqueness and once are what the soundness theorem's reuse reads. Their points on
the thread axes are the defaults there, and each fact sets them from the binding's type and a
closure literal's captures (`Modes.threads`, `Stilt.Modes.Threads`): no reuse reads portability or
contention.
-/

namespace Stilt

/-- What the modes of a body depend on beyond it: the program's declarations,
which parameters its functions consume (values.consumed-parameters), and which of their
parameters are `once` (modes.once-parameters). -/
structure ModeEnv where
  decls : Decls
  consumed : Consumed
  onceParams : OnceParams

/-- The facts that a program's bodies read: its declarations', solved over
its call graph. -/
def Program.modeEnv (p : Program) : ModeEnv := ⟨p.decls, p.decls.consumed, p.decls.onceParams⟩

/-- The context of an expression in a body. -/
structure ModeCtx where
  /-- Whether a mark of each variable may hand its storage over. -/
  reuse : Name → Bool
  /-- The part of the expression's value that leaves the function, if any
  does (modes.escaping). -/
  out : Option (List Sel)
  /-- Whether the expression, if it is a closure literal, is `once` (modes.once-closures). -/
  once : Bool
  /-- Whether the expression, if it is a closure literal, is the binding that
  a `let` or `var` names. -/
  bound : Bool
  /-- The `inout` parameters in scope, to which an assignment stores its value
  (modes.escaping). -/
  inouts : List Name
  /-- The bindings of the body that the inference calls shared (modes.shared-writes). -/
  shared : List Name

/-- The context of a part of an expression, whose value leaves as `out` says. -/
def ModeCtx.inner (k : ModeCtx) (out : Option (List Sel)) : ModeCtx :=
  { k with out, once := false, bound := false }

/-- The `inout` parameters in scope inside the scope of bindings `ys`. -/
def ModeCtx.hide (k : ModeCtx) (ys : List Name) : List Name := k.inouts.filter (!ys.contains ·)

/-- `f` with `x` given `b`. -/
def update (f : Name → Bool) (x : Name) (b : Bool) : Name → Bool :=
  fun y => if y == x then b else f y

namespace ModeEnv

variable (M : ModeEnv)

/-- The bindings of a body with parameters `ps`, its parameters and those it makes outside its
closure literals, each with its type and whether it may be modified. -/
def binders (ps : List Param) (body : Expr) : List (Name × Option Ty × Bool) :=
  ps.map (fun p => (p.name, some p.type, p.mode == .inout)) ++ body.bodyBinders

/-- Whether a binding of type `τ`, or of a type the core doesn't carry, which counts as one,
is of a copy-on-write type (modes.copy-on-write-types). -/
def cowOf (τ : Option Ty) : Bool := M.decls.cow (τ.getD .str)

/-- The bindings of a body with parameters `ps` that the inference calls shared
(modes.shared-writes): a `var` or an `inout` parameter of a copy-on-write type with a shared
modification, which the walk of the binding finds, or whose value is a copy of a part of
another binding that it reads after the modification, which that binding's walk finds; and any
binding whose value `Shared.new` takes while it might still read it, which its walk finds. A
`when`'s names are `var` bindings. Each binding's walk reads the body from its start (`walk`). -/
def bodyShared (ps : List Param) (body : Expr) : List Name :=
  let bs := binders ps body
  let modifiable := fun z => bs.any fun (y, τ, m) => y == z && m && M.cowOf τ
  bs.flatMap fun (x, τ, m) =>
    if M.cowOf τ then
      let w := walk M.decls M.consumed (inoutNames ps) x (τ.getD .str) body (ps.map (·.name))
      (if m && w.shared then [x] else []) ++ w.mirrored.filter fun z => z == x || modifiable z
    else []

/-- The modes of a `let` or `var` binding `y` of type `τ`, in the context `k`:
its locality (modes.escaping and modes.not-escaping), its uniqueness if it is a `var` (modes.copy-on-write-types, modes.copies and modes.shared-writes),
and, if it binds a closure literal, whether that closure is `once`
(modes.once-closures). Its thread axes are at their defaults, which its fact sets from its
type (`Modes.threads`); no reuse reads them. -/
def bindingModes (k : ModeCtx) (y : Name) (τ : Ty) (isVar : Bool) (init body : Expr) : Modes :=
  { Modes.default init.isClosure with
    locality := localityOf M.decls M.consumed k.inouts y τ k.out body
    uniqueness := if isVar && k.shared.contains y then .shared else .unique
    once := if init.isClosure then
      some (if boundOnce M.onceParams isVar y init body then .once else .many) else none }

/-- The modes of a closure literal in the context `k`: it escapes where its value leaves
(modes.escaping and modes.not-escaping), and is `once` as its context says (modes.once-closures),
which for a literal that a `let` or `var` binds is the binding's (`initCtx`). Its thread axes are
at their defaults, as `bindingModes` says. -/
def closureModes (k : ModeCtx) : Modes :=
  { Modes.default true with
    locality := if k.out.isSome then .escapes else .local
    once := some (if k.once then .once else .many) }

/-- The modes of a parameter of a body with parameters `ps`: its locality is
its consumption (modes.escaping), an `inout` one has a uniqueness (modes.shared-writes), and one of
function type is `once` when the body uses it once (modes.once-parameters). Its thread axes are at
their defaults, as `bindingModes` says. -/
def paramModes (ps : List Param) (body : Expr) (p : Param) : Modes :=
  { Modes.default p.type.isFn with
    locality := paramLocality M.decls M.consumed (inoutNames ps) body p
    uniqueness := if p.mode == .inout && (M.bodyShared ps body).contains p.name then .shared
      else .unique
    once := if p.type.isFn then
      some (if body.use M.onceParams p.name == .once then .once else .many) else none }

/-- Whether a parameter of a body with parameters `ps` may give its storage up
at a last use: a `let` parameter whose modes are `local` and `unique` (`Modes.reuses`). An
`inout` parameter's storage is its caller's. -/
def paramReuse (ps : List Param) (body : Expr) (p : Param) : Bool :=
  p.mode == .let && (M.paramModes ps body p).reuses

/-- Which variables of a body with parameters `ps` may give their storage up:
its `let` parameters whose modes are `local` and `unique`, and the others as `base` says. -/
def reuseOf (ps : List Param) (body : Expr) (base : Name → Bool) : Name → Bool := fun y =>
  match ps.find? (·.name == y) with
  | some p => M.paramReuse ps body p
  | none => base y

/-- Whether a `let` or `var` binding `y` may give its storage up: its modes are `local`
and `unique` (`Modes.reuses`). -/
def bindingReuse (k : ModeCtx) (y : Name) (τ : Ty) (isVar : Bool) (init body : Expr) : Bool :=
  (M.bindingModes k y τ isVar init body).reuses

/-- The context of the initializer of a binding `y`: a closure literal there
leaves the function where `y` does (modes.not-escaping), is `once` as modes.once-closures says, and is
the binding `y` names, whose modes give its point on the once axis. -/
def initCtx (k : ModeCtx) (y : Name) (τ : Ty) (isVar : Bool) (init body : Expr) : ModeCtx :=
  { k.inner (if init.isClosure &&
      body.leaves ⟨.escape, M.consumed, y, fun _ => true, k.inouts.filter (· != y)⟩ k.out
      then some [] else none) with
    once := (M.bindingModes k y τ isVar init body).runsOnce, bound := true }

/-- The context of the part at position `n` of an expression in the context
`k`, in the order of `Stilt.Modes.Traverse`. A closure literal's body is a
body of its own, whose result leaves it, and which owns its captures when the
closure's modes are `once` (`Modes.runsOnce`, modes.once-parameters). -/
def child (k : ModeCtx) : Expr → Nat → ModeCtx
  | .field _ f, _ => k.inner (k.out.map (.field f :: ·))
  | .index _ _, 0 => k.inner (k.out.map (.elem :: ·))
  | .record .., _ | .variant .., _ | .list .., _ | .raise _, _ | .perform _ _, _ | .assign .., 1 => k.inner (some [])
  | .closure ps _ _ body, _ =>
    ⟨M.reuseOf ps body fun _ => (closureModes k).runsOnce, some [], false, false, inoutNames ps,
      M.bodyShared ps body⟩
  | .call f _ _, 0 => { k.inner none with once := f.isClosure }
  | .call f _ _, n + 1 =>
    { k.inner (if consumesArg M.consumed f n then some [] else none) with
      once := passesOnce M.onceParams f n }
  | .letIn y τ init body, 0 => M.initCtx k y τ false init body
  | .varIn y τ init body, 0 => M.initCtx k y τ true init body
  | .letIn y τ init body, _ =>
    { k.inner k.out with
      reuse := update k.reuse y (M.bindingReuse k y τ false init body), inouts := k.hide [y] }
  | .varIn y τ init body, _ =>
    { k.inner k.out with
      reuse := update k.reuse y (M.bindingReuse k y τ true init body), inouts := k.hide [y] }
  | .seq .., 1 | .withH _ _ .., 1 | .if .., 1 | .if .., 2 | .try _, _ | .form _ _, _ | .tryCatch .., 0 => k.inner k.out
  | .match _ _ arms, n + 1 =>
    let binders := (arms[n]?.map (·.binders)).getD []
    { k.inner k.out with
      reuse := fun y => !binders.contains y && k.reuse y, inouts := k.hide binders }
  | .for y _ _ _, 1 =>
    { k.inner none with
      reuse := update k.reuse y false, inouts := k.hide [y] }
  | .tryCatch _ _ y _ _, _ =>
    { k.inner k.out with reuse := update k.reuse y false, inouts := k.hide [y] }
  | _, _ => k.inner none

/-- The context of a body with parameters `ps`, whose result leaves it. -/
def start (ps : List Param) (body : Expr) : ModeCtx :=
  ⟨M.reuseOf ps body fun _ => false, some [], false, false, inoutNames ps, M.bodyShared ps body⟩

end ModeEnv

/-! ## Facts -/

/-- A binding of the model (modes.bindings-and-axes). A closure literal that a `let` or
`var` binds is that binding. -/
inductive Binder where
  | «let» (name : Name)
  | «var» (name : Name)
  | param (name : Name)
  | closure
  deriving DecidableEq, Repr

/-- A binding and its modes. -/
structure Fact where
  binder : Binder
  modes : Modes
  deriving DecidableEq, Repr

/-- The words `show` prints of a fact (modes.show): only the modes other
than the default, a parameter's locality as its consumption, and nothing of
the locality of a closure literal that no binding names. -/
def Fact.words (f : Fact) : List String :=
  match f.binder with
  | .param _ => f.modes.words.map fun w => if w == "escapes" then "consumes" else w
  | .closure => f.modes.words.filter (· != "escapes")
  | _ => f.modes.words

/-- A binding at its defaults prints nothing. -/
theorem Fact.words_default (b : Binder) (closure : Bool) :
    (Fact.mk b (Modes.default closure)).words = [] := by
  cases b <;> simp [Fact.words, Modes.words_default]

namespace ModeEnv

variable (M : ModeEnv)

/-- The context of an expression for its facts: the context of its modes, and what each thread
axis knows of the bindings in scope, portability's and contention's. -/
abbrev FactCtx := ModeCtx × AxisScope × AxisScope

/-- The context of the part at position `n` of an expression. -/
def factChild (k : FactCtx) (e : Expr) (n : Nat) : FactCtx :=
  (M.child k.1 e n, axisChild M.decls.fixedTy k.2.1 e n, axisChild M.decls.contended k.2.2 e n)

/-- The modes `m` of a binding of type `τ` whose initializer is `init`, with its points on the
thread axes from its type, or from its captures when it binds a closure literal. -/
def boundThreads (k : FactCtx) (m : Modes) (τ : Ty) (init : Expr) : Modes :=
  m.threads (bindingAxis M.decls.fixedTy k.2.1 τ init) (bindingAxis M.decls.contended k.2.2 τ init)

/-- The facts that an expression in the context `k` gives of itself: those of
the binding it makes, if it makes one, with its thread axes from its type and its captures. -/
def visit (k : FactCtx) : Expr → List Fact
  | .letIn y τ init body => [⟨.let y, M.boundThreads k (M.bindingModes k.1 y τ false init body) τ init⟩]
  | .varIn y τ init body => [⟨.var y, M.boundThreads k (M.bindingModes k.1 y τ true init body) τ init⟩]
  | .closure ps r ρ body =>
    if k.1.bound then [] else
      [⟨.closure, (closureModes k.1).threads (closureAxis M.decls.fixedTy k.2.1 ps r ρ body)
        (closureAxis M.decls.contended k.2.2 ps r ρ body)⟩]
  | _ => []

/-- What the axis `has` knows of the parameters `ps` at the start of their body. -/
def paramAxes (has : Ty → Bool) (ps : List Param) : AxisScope := ps.map fun p => (p.name, has p.type)

/-- The facts of a body with parameters `ps`: its parameters', then its
bindings', in source order, closure literals' bodies among them. -/
def bodyFacts (ps : List Param) (body : Expr) : List Fact :=
  ps.map (fun p => ⟨.param p.name, (M.paramModes ps body p).threads (M.decls.fixedTy p.type)
      (M.decls.contended p.type)⟩) ++
    body.gather M.factChild M.visit
      (M.start ps body, paramAxes M.decls.fixedTy ps, paramAxes M.decls.contended ps)

end ModeEnv

/-- The modes of every binding of a program, by function, `main` last (modes.bindings-and-axes and modes.show). -/
def Program.facts (p : Program) : List (Name × List Fact) :=
  p.decls.fns.map (fun d => (d.name, p.modeEnv.bodyFacts d.params d.body)) ++
    [("main", p.modeEnv.bodyFacts [] p.main)]

/-- **A parameter's thread points are its type's** (modes.fixed-values, modes.contended-values
and modes.mode-crossing): it is `contended` exactly when its type holds a `Shared<T>`, and
`fixed` exactly when its type holds a view. -/
theorem ModeEnv.bodyFacts_param (M : ModeEnv) (ps : List Param) (body : Expr) (p : Param)
    (hp : p ∈ ps) : ∃ f ∈ M.bodyFacts ps body, f.binder = .param p.name ∧
      (f.modes.contention = .contended ↔ M.decls.contended p.type = true) ∧
      (f.modes.portability = .fixed ↔ M.decls.fixedTy p.type = true) := by
  refine ⟨_, List.mem_append_left _ (List.mem_map_of_mem hp), rfl, ?_, ?_⟩ <;>
    simp only [Modes.threads] <;> split <;> simp_all

end Stilt
