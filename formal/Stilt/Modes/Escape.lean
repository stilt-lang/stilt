import Stilt.Modes.Uses

/-!
# Leaving the function

Where a binding's value leaves the function that binds it: locality (modes.escaping and modes.not-escaping), and consumption (values.consumed-parameters), which modes.escaping makes the
locality of a parameter.

Both read one traversal, `Expr.leaves`, which follows the value of each part
of a body to where it goes: `out` is the part of that value that leaves the
function, if any of it does. The function's result leaves it, a `return`'s value among them; a record, list
or variant literal stores its parts in a value, and so does an assignment to an
`inout` parameter, to a part of another binding or through an index, while an
assignment to the whole of another local copies (modes.escaping and modes.copies); an argument
leaves with the parameter that its callee consumes; an `inout` argument comes
back (modes.not-escaping).
The two lists of uses differ in three places, which `Reading` chooses:

* modes.escaping counts a raise, and a capture by a closure literal that escapes;
* values.passing-values counts a rebinding with `var`, and a capture by any closure
  literal, which stores the value in the closure.

A callee that names no declared function, a closure or a parameter of
function type, consumes every argument: the model doesn't know its body, and
counting the argument as leaving is the conservative reading.
-/

namespace Stilt

/-- Which list of uses decides whether a value leaves: modes.escaping's, for
`let` and `var` bindings and closure literals, or consumption's's, for
parameters. -/
inductive Reading where
  | escape
  | consume
  deriving DecidableEq, Repr

/-- Which parameters of the program's functions are consumed (values.consumed-parameters): of the function with this name, at this position. -/
abbrev Consumed := Name → Nat → Bool

/-- Whether the argument at position `n` of a call is consumed: the callee
names a function that consumes its parameter there, or names none. -/
def consumesArg (C : Consumed) : Expr → Nat → Bool
  | .fnRef g _ _, n => C g n
  | _, _ => true

/-- What `Expr.leaves` asks about: the binding `name`, of which a part
`sels` counts when `counts sels` holds, under a reading and the program's
consumption, in a body whose `inout` parameters in scope are `inouts`. -/
structure Leaving where
  reading : Reading
  consumed : Consumed
  name : Name
  counts : List Sel → Bool
  inouts : List Name

/-- The same question about another binding, of which every part counts. -/
def Leaving.about (L : Leaving) (y : Name) : Leaving :=
  { L with name := y, counts := fun _ => true }

/-- The same question inside the scope of bindings `ys`, which hide the
`inout` parameters of their names. -/
def Leaving.hide (L : Leaving) (ys : List Name) : Leaving :=
  { L with inouts := L.inouts.filter (!ys.contains ·) }

/-- The names of the `inout` parameters of a body. -/
def inoutNames (ps : List Param) : List Name := (ps.filter (·.mode == .inout)).map (·.name)

/-- Whether an assignment to the place `y` and `path` stores its value where
it leaves the function: in an `inout` parameter, in a part of another binding,
or through an index. An assignment to the whole of another local is a copy
(modes.escaping and modes.copies). -/
def Leaving.stores (L : Leaving) (y : Name) (path : List Projection) : Bool :=
  L.inouts.contains y || (y != L.name && !path.isEmpty) ||
    path.any fun p => (Projection.fieldName? p).isNone

mutual

/-- Whether the binding `L.name` leaves the function in `e`, when the part
`out` of `e`'s value leaves it, if any part does. -/
def Expr.leaves (L : Leaving) (out : Option (List Sel)) : Expr → Bool
  | .var y | .move y => y == L.name && out.any L.counts
  | .int _ | .bool _ | .unit | .break | .continue | .fnRef _ _ _ | .method _ _ _ => false
  | .record _ fields => fieldsLeave L fields
  | .variant _ _ es | .list _ es | .op _ es | .view es => exprsLeave L es
  | .field e f => e.leaves L (out.map (.field f :: ·))
  | .index e i => e.leaves L (out.map (.elem :: ·)) || i.leaves L none
  | .closure ps _ _ body =>
    !hides ps L.name && body.occurs L.name && (L.reading == .consume || out.isSome)
  | .call f args _ => f.leaves L none || argsLeave L (consumesArg L.consumed f) 0 args
  | .letIn y _ init body =>
    init.leaves L (if init.isClosure && L.reading == .escape &&
        body.leaves ((L.hide [y]).about y) out then some [] else none) ||
      (y != L.name && body.leaves (L.hide [y]) out)
  | .varIn y _ init body =>
    init.leaves L (if L.reading == .consume || init.isClosure &&
        body.leaves ((L.hide [y]).about y) out then some [] else none) ||
      (y != L.name && body.leaves (L.hide [y]) out)
  | .assign ⟨y, path⟩ v =>
    pathLeave L path || v.leaves L (if L.stores y path then some [] else none)
  | .seq a b => a.leaves L none || b.leaves L out
  | .if c _ a b => c.leaves L none || a.leaves L out || b.leaves L out
  | .match e _ arms => e.leaves L none || armsLeave L out arms
  | .for y _ e body => e.leaves L none || (y != L.name && body.leaves (L.hide [y]) none)
  | .raise e => e.leaves L (if L.reading == .escape then some [] else none)
  | .try e => e.leaves L out
  | .tryCatch e _ y h _ => e.leaves L out || (y != L.name && h.leaves (L.hide [y]) out)
  | .while c body => c.leaves L none || body.leaves L none
  | .loop body => body.leaves L none
  | .return e => e.leaves L (some [])
  | .perform _ e => e.leaves L (some [])
  | .withH _ _ h b => h.leaves L (some []) || b.leaves L out
  | .held ns hs body =>
    exprsLeave L hs || (!(ns.any (·.1 == L.name)) && body.leaves (L.hide (ns.map (·.1))) out)

/-- Whether the binding leaves in a list of expressions whose values are
stored in a value. -/
def exprsLeave (L : Leaving) : List Expr → Bool
  | [] => false
  | e :: es => e.leaves L (some []) || exprsLeave L es

/-- Whether the binding leaves in the fields of a record literal, which store
their values in it. -/
def fieldsLeave (L : Leaving) : List (Name × Expr) → Bool
  | [] => false
  | (_, e) :: fields => e.leaves L (some []) || fieldsLeave L fields

/-- Whether the binding leaves in a call's arguments, from position `n`: an
argument leaves when its parameter is consumed, and an `inout` one comes
back (modes.not-escaping). -/
def argsLeave (L : Leaving) (consumed : Nat → Bool) (n : Nat) : List Arg → Bool
  | [] => false
  | .value e :: args =>
    e.leaves L (if consumed n then some [] else none) || argsLeave L consumed (n + 1) args
  | .inout ⟨_, path⟩ :: args => pathLeave L path || argsLeave L consumed (n + 1) args

/-- Whether the binding leaves in the indexes of a place. -/
def pathLeave (L : Leaving) : List Projection → Bool
  | [] => false
  | .field _ :: path => pathLeave L path
  | .index i :: path => i.leaves L none || pathLeave L path

/-- Whether the binding leaves in the arms of a `match`; an arm that binds its
name hides it. -/
def armsLeave (L : Leaving) (out : Option (List Sel)) : List Arm → Bool
  | [] => false
  | ⟨_, binders, body⟩ :: arms =>
    (!binders.contains L.name && body.leaves (L.hide binders) out) || armsLeave L out arms

end

/-! ## Consumption -/

/-- Whether a body with the `inout` parameters `inouts` consumes its parameter
`p`: returns it, stores it in a value, rebinds it with `var`, or passes it to a
parameter that `C` says is consumed (values.consumed-parameters). A value is stored as
modes.escaping says: in a literal, a variant, or an assignment that isn't to
the whole of another local. An `inout` parameter is never consumed: its value
goes back to the caller (values.inout-arguments). -/
def Expr.consumes (body : Expr) (C : Consumed) (inouts : List Name) (p : Param) : Bool :=
  p.mode == .let && body.leaves ⟨.consume, C, p.name, fun _ => true, inouts⟩ (some [])

/-- Whether the function `d` consumes its parameter `p` (values.consumed-parameters). -/
def FnDecl.consumes (d : FnDecl) (C : Consumed) (p : Param) : Bool :=
  d.body.consumes C (inoutNames d.params) p

namespace Decls

/-- One round of values.consumed-parameters: a parameter is consumed when its function's
body consumes it, with `C` for the parameters of its callees. -/
def consumeStep (D : Decls) (C : Consumed) : Consumed := fun g n =>
  match D.fn? g with
  | some d =>
    match d.params[n]? with
    | some p => d.consumes C p
    | none => false
  | none => false

/-- The consumed parameters of the program (values.consumed-parameters): the fixed point
over the call graph, from no parameter consumed. A round only adds consumed
parameters, so as many rounds as there are parameters reach it
(`Decls.consumed_fixed`). -/
def consumed (D : Decls) : Consumed := Nat.repeat D.consumeStep (D.slots + 1) fun _ _ => false

end Decls

/-! ## Locality -/

/-- The locality of a `let` or `var` binding or a closure literal `y` of type
`τ`, whose scope is `body` and whose scope's value leaves the function as
`out` says, in a body whose `inout` parameters in scope are `inouts` (modes.escaping and modes.not-escaping). A binding whose type isn't copy-on-write is `local`. -/
def localityOf (D : Decls) (C : Consumed) (inouts : List Name) (y : Name) (τ : Ty)
    (out : Option (List Sel)) (body : Expr) : Locality :=
  if D.cow τ && body.leaves ⟨.escape, C, y, D.cowPart τ, inouts.filter (· != y)⟩ out
  then .escapes else .local

/-- The locality of a parameter `p` of a function or closure literal whose body
is `body` and whose `inout` parameters are `inouts`: for a parameter of a
copy-on-write type, escaping is consumption (modes.escaping; values.consumed-parameters). -/
def paramLocality (D : Decls) (C : Consumed) (inouts : List Name) (body : Expr) (p : Param) :
    Locality :=
  if D.cow p.type && body.consumes C inouts p then .escapes else .local

/-- **A parameter's locality is its consumption** (modes.escaping): a
parameter of a copy-on-write type escapes exactly when its function consumes
it, as values.consumed-parameters reads the body. -/
theorem paramLocality_escapes_iff (D : Decls) (C : Consumed) (d : FnDecl) (p : Param)
    (hcow : D.cow p.type = true) :
    paramLocality D C (inoutNames d.params) d.body p = .escapes ↔ d.consumes C p = true := by
  unfold paramLocality FnDecl.consumes
  cases h : d.body.consumes C (inoutNames d.params) p <;> simp [hcow]

/-- A parameter of a type that isn't copy-on-write is `local` (modes.escaping). -/
theorem paramLocality_of_not_cow (D : Decls) (C : Consumed) (inouts : List Name) (body : Expr)
    (p : Param) (hcow : D.cow p.type = false) : paramLocality D C inouts body p = .local := by
  simp [paramLocality, hcow]

/-- A round of values.consumed-parameters asks of each parameter what its locality reads:
whether its function's body consumes it. -/
theorem consumeStep_fn {D : Decls} {C : Consumed} {g : Name} {d : FnDecl} (hd : D.fn? g = some d)
    {n : Nat} {p : Param} (hp : d.params[n]? = some p) : D.consumeStep C g n = d.consumes C p := by
  simp [Decls.consumeStep, hd, hp]

end Stilt
