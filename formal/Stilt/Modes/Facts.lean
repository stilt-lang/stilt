import Stilt.Modes.Uniqueness
import Stilt.Modes.Traverse

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
may give their storage up at a last use: a `local`, `unique` binding, or a
capture of a `once` closure, which its body owns (modes.once-closures;
modes.once-parameters). `Stilt.Modes.Agreement` reads the last of these.
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
another binding that it reads after the modification, which that binding's walk finds. Each
binding's walk reads the body from its start (`walk`). -/
def bodyShared (ps : List Param) (body : Expr) : List Name :=
  let bs := binders ps body
  let modifiable := fun z => bs.any fun (y, τ, m) => y == z && m && M.cowOf τ
  bs.flatMap fun (x, τ, m) =>
    if M.cowOf τ then
      let w := walk M.decls M.consumed (inoutNames ps) x (τ.getD .str) body
      (if m && w.shared then [x] else []) ++ w.mirrored.filter modifiable
    else []

/-- Whether a parameter of a body with parameters `ps` may give its storage up
at a last use: a `let` parameter that is `local` (modes.escaping), as every
`let` parameter is `unique`. -/
def paramReuse (ps : List Param) (body : Expr) (p : Param) : Bool :=
  p.mode == .let && paramLocality M.decls M.consumed (inoutNames ps) body p == .local

/-- Which variables of a body with parameters `ps` may give their storage up:
its `local` `let` parameters, and the others as `base` says. -/
def reuseOf (ps : List Param) (body : Expr) (base : Name → Bool) : Name → Bool := fun y =>
  match ps.find? (·.name == y) with
  | some p => M.paramReuse ps body p
  | none => base y

/-- Whether a `let` or `var` binding `y` may give its storage up: it is `local`
and `unique` (modes.escaping and modes.shared-writes). -/
def bindingReuse (k : ModeCtx) (y : Name) (τ : Ty) (isVar : Bool) (body : Expr) : Bool :=
  localityOf M.decls M.consumed k.inouts y τ k.out body == .local &&
    (!isVar || !k.shared.contains y)

/-- The context of the initializer of a binding `y`: a closure literal there
leaves the function where `y` does (modes.not-escaping), is `once` as modes.once-closures says, and is
the binding `y` names. -/
def initCtx (k : ModeCtx) (y : Name) (isVar : Bool) (init body : Expr) : ModeCtx :=
  { k.inner (if init.isClosure &&
      body.leaves ⟨.escape, M.consumed, y, fun _ => true, k.inouts.filter (· != y)⟩ k.out
      then some [] else none) with
    once := boundOnce M.onceParams isVar y init body, bound := true }

/-- The context of the part at position `n` of an expression in the context
`k`, in the order of `Stilt.Modes.Traverse`. A closure literal's body is a
body of its own, whose result leaves it, and which owns its captures when the
closure is `once` (modes.once-parameters). -/
def child (k : ModeCtx) : Expr → Nat → ModeCtx
  | .field _ f, _ => k.inner (k.out.map (.field f :: ·))
  | .index _ _, 0 => k.inner (k.out.map (.elem :: ·))
  | .record .., _ | .variant .., _ | .list .., _ | .raise _, _ | .perform _ _, _ | .assign .., 1 => k.inner (some [])
  | .closure ps _ _ body, _ =>
    ⟨M.reuseOf ps body fun _ => k.once, some [], false, false, inoutNames ps, M.bodyShared ps body⟩
  | .call f _ _, 0 => { k.inner none with once := f.isClosure }
  | .call f _ _, n + 1 =>
    { k.inner (if consumesArg M.consumed f n then some [] else none) with
      once := passesOnce M.onceParams f n }
  | .letIn y _ init body, 0 => M.initCtx k y false init body
  | .varIn y _ init body, 0 => M.initCtx k y true init body
  | .letIn y τ _ body, _ =>
    { k.inner k.out with
      reuse := update k.reuse y (M.bindingReuse k y τ false body), inouts := k.hide [y] }
  | .varIn y τ _ body, _ =>
    { k.inner k.out with
      reuse := update k.reuse y (M.bindingReuse k y τ true body), inouts := k.hide [y] }
  | .seq .., 1 | .withH _ _ .., 1 | .if .., 1 | .if .., 2 | .try _, _ | .tryCatch .., 0 => k.inner k.out
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

/-- The modes of a `let` or `var` binding `y` of type `τ`, in the context `k`:
its locality (modes.escaping and modes.not-escaping), its uniqueness if it is a `var` (modes.copy-on-write-types, modes.copies and modes.shared-writes),
and, if it binds a closure literal, whether that closure is `once`
(modes.once-closures). -/
def bindingModes (k : ModeCtx) (y : Name) (τ : Ty) (isVar : Bool) (init body : Expr) : Modes :=
  { locality := localityOf M.decls M.consumed k.inouts y τ k.out body
    uniqueness := if isVar && k.shared.contains y then .shared else .unique
    once := if init.isClosure then
      some (if boundOnce M.onceParams isVar y init body then .once else .many) else none
    portability := portabilityOf τ []
    contention := contentionOf τ [] }

/-- The modes of a closure literal of type `τ` that no binding names: it
escapes where its value leaves (modes.escaping and modes.not-escaping), and is `once` as its context
says (modes.once-closures). -/
def closureModes (k : ModeCtx) (τ : Ty) : Modes :=
  ⟨if k.out.isSome then .escapes else .local, .unique, some (if k.once then .once else .many),
    portabilityOf τ [], contentionOf τ []⟩

/-- The modes of a parameter of a body with parameters `ps`: its locality is
its consumption (modes.escaping), an `inout` one has a uniqueness (modes.shared-writes), and one of
function type is `once` when the body uses it once (modes.once-parameters). -/
def paramModes (ps : List Param) (body : Expr) (p : Param) : Modes :=
  { locality := paramLocality M.decls M.consumed (inoutNames ps) body p
    uniqueness := if p.mode == .inout && (M.bodyShared ps body).contains p.name then .shared
      else .unique
    once := if p.type.isFn then
      some (if body.use M.onceParams p.name == .once then .once else .many) else none
    portability := portabilityOf p.type []
    contention := contentionOf p.type [] }

/-- The facts that an expression in the context `k` gives of itself: those of
the binding it makes, if it makes one. -/
def visit (k : ModeCtx) : Expr → List Fact
  | .letIn y τ init body => [⟨.let y, M.bindingModes k y τ false init body⟩]
  | .varIn y τ init body => [⟨.var y, M.bindingModes k y τ true init body⟩]
  | .closure ps r ρ _ =>
    if k.bound then [] else [⟨.closure, closureModes k (.fn (ps.map Param.sig) r ρ)⟩]
  | _ => []

/-- The facts of a body with parameters `ps`: its parameters', then its
bindings', in source order, closure literals' bodies among them. -/
def bodyFacts (ps : List Param) (body : Expr) : List Fact :=
  ps.map (fun p => ⟨.param p.name, M.paramModes ps body p⟩) ++
    body.gather M.child M.visit (M.start ps body)

end ModeEnv

/-- The modes of every binding of a program, by function, `main` last (modes.bindings-and-axes and modes.show). -/
def Program.facts (p : Program) : List (Name × List Fact) :=
  p.decls.fns.map (fun d => (d.name, p.modeEnv.bodyFacts d.params d.body)) ++
    [("main", p.modeEnv.bodyFacts [] p.main)]

/-- **No binding of the calculus is contended** (modes.contended-values and
modes.mode-crossing), and only a binding of a view type is fixed (modes.fixed-values and
views.fixed): every fact of every body is `calm`, and `portable` unless its binding has
a view type. -/
theorem ModeEnv.bodyFacts_calm (M : ModeEnv) (ps : List Param) (body : Expr) :
    ∀ f ∈ M.bodyFacts ps body, f.modes.contention = .calm ∧
      (f.modes.portability = .fixed → ∃ τ σ, τ = .view σ ∧ f.modes.portability = portabilityOf τ []) := by
  intro f hf
  rcases List.mem_append.1 hf with h | h
  · obtain ⟨p, -, rfl⟩ := List.mem_map.1 h
    refine ⟨calm p.type [], fun hfix => ?_⟩
    obtain ⟨σ, hσ⟩ := (portabilityOf_fixed_iff _).1 hfix
    exact ⟨p.type, σ, hσ, rfl⟩
  · refine Expr.gather_all M.child M.visit
      (fun f : Fact => f.modes.contention = .calm ∧ (f.modes.portability = .fixed →
        ∃ τ σ, τ = .view σ ∧ f.modes.portability = portabilityOf τ []))
      (fun k e f hf => ?_) body _ f h
    cases e <;> simp only [ModeEnv.visit, List.not_mem_nil] at hf
    case letIn y τ _ _ | varIn y τ _ _ =>
      rw [List.mem_singleton.1 hf]
      refine ⟨calm τ [], fun hfix => ?_⟩
      obtain ⟨σ, hσ⟩ := (portabilityOf_fixed_iff _).1 hfix
      exact ⟨τ, σ, hσ, rfl⟩
    case closure ps r ρ _ =>
      split at hf
      · exact absurd hf List.not_mem_nil
      · rw [List.mem_singleton.1 hf]
        refine ⟨calm (.fn (ps.map Param.sig) r ρ) [], fun hfix => ?_⟩
        obtain ⟨σ, hσ⟩ := (portabilityOf_fixed_iff (.fn (ps.map Param.sig) r ρ)).1 hfix
        cases hσ

/-- Every binding of a program prints no `contended`, and prints `fixed` only when it
has a view type (modes.facts-suite, Required tests). -/
theorem Program.facts_calm (p : Program) :
    ∀ nf ∈ p.facts, ∀ f ∈ nf.2, f.modes.contention = .calm ∧
      (f.modes.portability = .fixed → ∃ τ σ, τ = .view σ ∧ f.modes.portability = portabilityOf τ []) := by
  intro nf hnf f hf
  rcases List.mem_append.1 hnf with h | h
  · obtain ⟨d, -, rfl⟩ := List.mem_map.1 h
    exact p.modeEnv.bodyFacts_calm _ _ f hf
  · rw [List.mem_singleton.1 h] at hf
    exact p.modeEnv.bodyFacts_calm _ _ f hf

end Stilt
