import Stilt.Modes.Types

/-!
# Uses

Where a body uses a variable, read from its source: the occurrences of the
name that refer to the binding, which an inner binding of the same name hides.
A closure literal uses what its body uses but its own parameters, and
captures it (expressions.capture), as the model's closures do when they run
(`captureOf`).

`Expr.use` sums a variable's uses as modes.once-closures and modes.once-parameters count them: none, one that
is a call outside every loop and every closure literal, or a pass to a `once`
parameter of a function the call names, or more. A loop's body and a closure
literal may run more than once, so any use there counts as many.
-/

namespace Stilt

/-- Whether a closure literal's parameters hide a name. -/
def hides (ps : List Param) (x : Name) : Bool := ps.any (·.name == x)

/-- How a variable is used, as modes.once-closures and modes.once-parameters count it. -/
inductive Use where
  /-- Not at all. -/
  | none
  /-- Once: a call outside every loop and closure literal, or a pass to a
  `once` parameter. -/
  | once
  /-- In any other way, or more than once. -/
  | many
  deriving DecidableEq, Repr

/-- Two parts of a body use a variable as their uses together do. -/
def Use.add : Use → Use → Use
  | .none, u => u
  | u, .none => u
  | _, _ => .many

/-- A use inside a loop's body or a closure literal may run again (modes.once-closures and modes.once-parameters). -/
def Use.again : Use → Use
  | .none => .none
  | _ => .many

/-- Which parameters of the program's functions are `once` (modes.once-parameters): of the
function with this name, at this position. -/
abbrev OnceParams := Name → Nat → Bool

/-- Whether the argument at position `n` of a call goes to a `once` parameter:
the callee names a function whose parameter there is `once`. -/
def passesOnce (O : OnceParams) : Expr → Nat → Bool
  | .fnRef g _ _, n => O g n
  | _, _ => false

/-- The variable an expression reads, if it is one. -/
def Expr.var? : Expr → Option Name
  | .var x | .move x => some x
  | _ => none

/-- Whether an expression is a closure literal. -/
def Expr.isClosure : Expr → Bool
  | .closure .. => true
  | _ => false

mutual

/-- How `e` uses the variable `f`, when `O` gives the `once` parameters of the
program's functions (modes.once-closures and modes.once-parameters). -/
def Expr.use (O : OnceParams) (f : Name) : Expr → Use
  | .var y | .move y => if y == f then .many else .none
  | .int _ | .bool _ | .unit | .break | .continue | .fnRef _ _ _ | .method _ _ _ => .none
  | .record _ _ fields => fieldsUse O f fields
  | .variant _ _ _ es | .list _ es | .op _ es | .view es => exprsUse O f es
  | .field e _ => e.use O f
  | .index e i => (e.use O f).add (i.use O f)
  | .closure ps _ _ body => if hides ps f then .none else (body.use O f).again
  | .call callee args _ =>
    (if callee.var? == some f then .once else callee.use O f).add
      (argsUse O f (passesOnce O callee) 0 args)
  | .letIn y _ init body | .varIn y _ init body =>
    (init.use O f).add (if y == f then .none else body.use O f)
  | .held ns hs body =>
    (exprsUse O f hs).add (if ns.any (·.1 == f) then .none else body.use O f)
  | .assign ⟨y, path⟩ v =>
    Use.add (if y == f then .many else .none) ((pathUse O f path).add (v.use O f))
  | .seq a b => (a.use O f).add (b.use O f)
  | .if c _ a b => (c.use O f).add ((a.use O f).add (b.use O f))
  | .match e _ arms => (e.use O f).add (armsUse O f arms)
  | .for y _ e body => (e.use O f).add (if y == f then .none else (body.use O f).again)
  | .raise e | .perform _ e | .try e | .return e => e.use O f
  | .while c body => ((c.use O f).add (body.use O f)).again
  | .loop body => (body.use O f).again
  | .tryCatch e _ y h _ => (e.use O f).add (if y == f then .none else h.use O f)
  | .withH _ _ h b => (h.use O f).add (b.use O f).again

/-- How a list of expressions uses `f`. -/
def exprsUse (O : OnceParams) (f : Name) : List Expr → Use
  | [] => .none
  | e :: es => (e.use O f).add (exprsUse O f es)

/-- How the fields of a record literal use `f`. -/
def fieldsUse (O : OnceParams) (f : Name) : List (Name × Expr) → Use
  | [] => .none
  | (_, e) :: fields => (e.use O f).add (fieldsUse O f fields)

/-- How a call's arguments use `f`, from position `n`: passing `f` itself to
a `once` parameter is one use (modes.once-closures and modes.once-parameters), and passing it `inout` is a use
other than a call. -/
def argsUse (O : OnceParams) (f : Name) (once : Nat → Bool) (n : Nat) : List Arg → Use
  | [] => .none
  | .value e :: args =>
    (if e.var? == some f then (if once n then .once else .many) else e.use O f).add
      (argsUse O f once (n + 1) args)
  | .inout ⟨y, path⟩ :: args =>
    Use.add (if y == f then .many else .none)
      ((pathUse O f path).add (argsUse O f once (n + 1) args))

/-- How the indexes of a place use `f`. -/
def pathUse (O : OnceParams) (f : Name) : List Projection → Use
  | [] => .none
  | .field _ :: path => pathUse O f path
  | .index i :: path => (i.use O f).add (pathUse O f path)

/-- How the arms of a `match` use `f`; an arm that binds `f` hides it. -/
def armsUse (O : OnceParams) (f : Name) : List Arm → Use
  | [] => .none
  | ⟨_, binders, body⟩ :: arms =>
    (if binders.contains f then .none else body.use O f).add (armsUse O f arms)

end

/-- Whether `e` uses `x` at all: whether its value or a closure it makes
depends on the binding. -/
def Expr.occurs (x : Name) (e : Expr) : Bool := e.use (fun _ _ => false) x != .none

/-- Whether an arm of a `match` uses `x`. -/
def armsOccur (x : Name) (arms : List Arm) : Bool :=
  arms.any fun arm => !arm.binders.contains x && arm.body.occurs x

/-! ## Once parameters -/

/-- Whether a type is a function type. -/
def Ty.isFn : Ty → Bool
  | .fn .. => true
  | _ => false

namespace Decls

/-- The parameters of the program's functions: each function's name, with each
position of its parameters. -/
def slotList (D : Decls) : List (Name × Nat) :=
  D.fns.flatMap fun d => (List.range d.params.length).map fun n => (d.name, n)

/-- The number of parameters of the program's functions. -/
def slots (D : Decls) : Nat := D.slotList.length

/-- One round of modes.once-parameters: a parameter of function type is `once` when its
function's body uses it once, with `O` for the parameters of its callees. -/
def onceStep (D : Decls) (O : OnceParams) : OnceParams := fun g n =>
  match D.fn? g with
  | some d =>
    match d.params[n]? with
    | some p => p.type.isFn && d.body.use O p.name == .once
    | none => false
  | none => false

/-- The `once` parameters of the program (modes.once-parameters): the fixed point over
the call graph, from every parameter `once`, as the implicit effects are
solved. A round only turns parameters `many`, so as many rounds as there are
parameters reach it (`Decls.onceParams_fixed`). -/
def onceParams (D : Decls) : OnceParams := Nat.repeat D.onceStep (D.slots + 1) fun _ _ => true

end Decls

/-- A closure literal bound by `let f` is `once` when `f` is used once in its
scope (modes.once-closures). -/
def boundOnce (O : OnceParams) (isVar : Bool) (f : Name) (init body : Expr) : Bool :=
  init.isClosure && !isVar && body.use O f == .once

end Stilt
