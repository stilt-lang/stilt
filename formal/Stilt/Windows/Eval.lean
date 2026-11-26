import Stilt.Windows.Memory

/-!
# The evaluator of windows

The evaluator of `Stilt.Semantics` with views made as windows (views.making-view): it is
`eval` in the model `Windows.memory` but where a view is made, where a window is read, and where
a value leaves the frames it was made in.

* `View.of(source, …)` and `View.all(source)`, once the source is evaluated as in the other
  models, make a window on the place it names when that takes no index; of a view, a window on
  what the view reads, its ranges in turn; of any other expression, a temporary that nothing
  can name or change, the part it reads, as in the other models, so the store of windows has
  the locations of the in-place model's.
* A call frees the callee's locations when it ends, and its value, returned or raised, reads
  each window on them first.
* An operation reads its operands through their windows, and so do indexing, a field, a `for`'s
  iterable and a `match`'s scrutinee: `copy` is the part a window reads
  (views.functions-of-views). A record or a list literal reads its elements through their
  windows, as no field or element of such a type is a view (views.view-types).
* A value that a performance passes to a handler, a handler's value, and the value of a
  `with`'s block, the error it raises and the value it returns are read through their windows,
  since they leave the frames whose storage the windows read (handlers.performing-operation).

A view passed to a call, bound, returned or raised stays a window. `Program.runWindows` reads
the error a run raises through its windows, at the end of the run: a raised window is
observed as its part.
-/

namespace Stilt

namespace Windows

/-- A value read through its windows, in the current state's store. -/
def resolveE (v : Value) : Eval (State × World) Value := Eval.inspect fun s => resolve s.1.store v

/-- Values read through their windows. -/
def resolveAllE (vs : List Value) : Eval (State × World) (List Value) :=
  Eval.inspect fun s => mapWindowsValues (fun loc path ranges => do
    resolve s.1.store (← part s.1.store loc path ranges)) vs

/-- The fields of a place that takes no index, as a path. -/
def fieldPath : List Projection → Option Path
  | [] => some []
  | .field f :: rest => (.field f :: ·) <$> fieldPath rest
  | .index _ :: _ => none

/-- Whether a value can be viewed: a string or a list (views.viewable-types). -/
def viewable : Value → Bool
  | .str _ | .list _ => true
  | _ => false

/-- The view of the place that `x` and an index-free path name, whose value `read` is: the
window the place holds, when it holds a view, for a view of a view reads what that view reads;
a window on the place, when its part holds no view and can be viewed; and otherwise the value
read, a temporary (views.making-view). -/
def windowAt (s : State) (x : Name) (path : Path) (read : Value) : Value :=
  match s.env.lookup x with
  | some r =>
    match cell s.store r.loc >>= (·.get (r.path ++ path)) with
    | .ok (.window loc p ranges) => .window loc p ranges
    | .ok v =>
      if (mapWindows (fun _ _ _ => .error .stuck) v).isOk && viewable v then
        .window r.loc (r.path ++ path) []
      else read
    | .error _ => read
  | none => read

/-- The source of a view, once its first operand is evaluated to `read`: a window on the place
the operand names, when it names one with no index (`windowAt`), or the value read, a
temporary that nothing can name or change (views.making-view). -/
def viewOf (s : State) (src : Expr) (read : Value) : Value :=
  match src.place? with
  | some ⟨x, projections⟩ =>
    match fieldPath projections with
    | some path => windowAt s x path read
    | none => read
  | none => read

/-- A view's source narrowed by its offsets: none for `View.all`, or a start and an end, checked
as `slice` checks them, from the window's start (views.making-view). A view of a temporary that
is no window is the part it reads, as nothing can name or change a temporary. -/
def narrow (st : List (Option Value)) : Value → List Value → Except Fault Value
  | .window loc p ranges, [] => .ok (.window loc p ranges)
  | .window loc p ranges, [.int a, .int b] => do
    let _ ← part st loc p (ranges ++ [(a, b)])
    pure (.window loc p (ranges ++ [(a, b)]))
  | .window .., _ => .error .stuck
  | v, ns => Op.view.apply (v :: ns)

/-- The parameters of a function value, as its declaration or its literal writes them. -/
def paramsOf (D : Decls) : Value → List Param
  | .closure _ ps _ _ _ => ps
  | .function f _ _ => ((D.fn? f).map (·.params)).getD []
  | _ => []

/-- Whether a binding of type `τ` keeps the views its value holds: when `τ` may hold one and
is no function type, whose closures read their captured views when they are made
(views.view-types). -/
def keepsView (D : Decls) (τ : Ty) : Bool :=
  τ.holdsView D && match τ with
    | .fn .. => false
    | _ => true

/-- A value bound to a binding or a parameter of type `τ`: kept as it is when `τ` keeps views,
and read through its windows otherwise. -/
def keep (D : Decls) (τ : Ty) (v : Value) : Eval (State × World) Value :=
  if keepsView D τ then pure v else resolveE v

/-- The arguments a call passes to the parameters `ps`, each `let` argument kept for its
parameter's type. -/
def passTo (D : Decls) : List Param → List Passed → Eval (State × World) (List Passed)
  | p :: ps, .value v :: args => do
    let w ← keep D p.type v
    let ws ← passTo D ps args
    pure (.value w :: ws)
  | p :: ps, .moved x v :: args => do
    let w ← keep D p.type v
    let ws ← passTo D ps args
    pure (.moved x w :: ws)
  | _ :: ps, a :: args => do
    let ws ← passTo D ps args
    pure (a :: ws)
  | _, args => pure args

/-- The store with each location from `n` on freed: the callee's own, when a call that
started at a store of length `n` ends (views.across-calls). -/
def freeFrom (n : Nat) (s : State × World) : State × World :=
  ({ s.1 with store := s.1.store.take n ++ (s.1.store.drop n).map fun _ => none }, s.2)

/-- A value with each window on a location from `n` on read through, in the store `st`. -/
def resolveFrom (st : List (Option Value)) (n : Nat) : Value → Except Fault Value :=
  mapWindows fun loc path ranges =>
    if n ≤ loc then do resolve st (← part st loc path ranges) else .ok (.window loc path ranges)

/-- The outcome of a call that started at a store of length `n`: the callee's locations freed,
the value it returns read through each window on one of them first, and the error it raises
read through all its windows. A view of a callee's copy of an argument reads what the copy
holds when the call ends, and no error is a view (views.escaping). -/
def _root_.Stilt.Outcome.settle (n : Nat) :
    Outcome (State × World) Value → Outcome (State × World) Value
  | .done v s =>
    match resolveFrom s.1.store n v with
    | .ok w => .done w (freeFrom n s)
    | .error f => .fault f (freeFrom n s)
  | .raised e s =>
    match resolve s.1.store e with
    | .ok w => .raised w (freeFrom n s)
    | .error f => .fault f (freeFrom n s)
  | .jumped j s => .jumped j (freeFrom n s)
  | .panicked k s => .panicked k (freeFrom n s)
  | .performed op v s k => .performed op v (freeFrom n s) fun w x => (k w x).settle n
  | .outOfFuel => .outOfFuel
  | .stuck => .stuck

/-- The outcome of a block under a handler, the error it raises and the value it returns read
through their windows in the store it ends with: a rest of the block resumed once more ends in
the frames of the rest resumed before it, where its windows would read other parts
(handlers.resuming). -/
def _root_.Stilt.Outcome.readEscapes :
    Outcome (State × World) Value → Outcome (State × World) Value
  | .raised e s =>
    match resolve s.1.store e with
    | .ok w => .raised w s
    | .error f => .fault f s
  | .jumped (.ret v) s =>
    match resolve s.1.store v with
    | .ok w => .jumped (.ret w) s
    | .error f => .fault f s
  | .performed op v s k => .performed op v s fun w x => (k w x).readEscapes
  | o => o

/-- Runs a block under a handler, its value, the error it raises and the value it returns read
through their windows (`Outcome.readEscapes`). -/
def underHandler (m : Eval (State × World) Value) : Eval (State × World) Value := fun s =>
  ((m >>= resolveE) s).readEscapes

/-- Calls a function value as `Eval.callAs` does, the callee's locations freed when the call
ends (`Outcome.settle`). -/
def callSettled (D : Decls) (run : Expr → Eval (State × World) Value) (control : Bool) (f : Value)
    (args : List Passed) : Eval (State × World) Value := fun s =>
  (Eval.callAs D memory run control f args s).settle s.1.store.length

/-- Calls a function value with its `let` arguments kept for its parameters' types, the
callee's locations freed when it ends, and its result, of type `result`, read through its
windows unless that is a view type (views.across-calls). -/
def call (D : Decls) (run : Expr → Eval (State × World) Value) (f : Value) (passed : List Passed)
    (result : Ty) : Eval (State × World) Value := do
  let args ← passTo D (paramsOf D f) passed
  let v ← callSettled D run false f args
  if result.isView D then pure v else resolveE v

/-- Runs the body of a `for` loop over the elements its iterable's windows read
(expressions.for-iterables and views.for-over-view). -/
def loop (run : Expr → Eval (State × World) Value) (x : Name) (iterable body : Expr) :
    Eval (State × World) Value := do
  let vs ← run iterable >>= resolveE >>= Eval.asList
  Eval.forEach (fun v => Eval.withVar memory x v (Eval.turn (run body))) vs
  pure .unit

end Windows

namespace Windows

/-- A step of the evaluator of windows on a form that builds or reads a value, `run` evaluating
its parts. -/
def evalValue (D : Decls) (run : Expr → Eval (State × World) Value) :
    Expr → Eval (State × World) Value
  | .var x | .move x => Eval.inspect fun s => readWindows s.1 x []
  | .int k => pure (.int k)
  | .bool b => pure (.bool b)
  | .unit => pure .unit
  | .record R _ fields => do
    let written ← Eval.fields run fields
    Eval.declare D R written >>= resolveE
  | .variant T _ C payload => do
    let vs ← Eval.list run payload
    pure (.variant T C vs)
  | .list _ es => do
    let vs ← Eval.list run es
    resolveE (.list vs)
  | .op o es => do
    let vs ← Eval.list run es >>= resolveAllE
    Eval.world memory (o.run vs)
  | .view es => match es with
    | src :: offsets => do
      let v ← run src
      let w ← Eval.inspect fun s => .ok (viewOf s.1 src v)
      let ns ← Eval.list run offsets
      Eval.inspect fun s => narrow s.1.store w ns
    | [] => Eval.fail .stuck
  | .field e f => do
    let v ← run e >>= resolveE
    Eval.ofExcept (v.get [.field f])
  | .index e i => do
    let v ← run e >>= resolveE
    let k ← run i >>= Eval.asInt
    Eval.ofExcept (v.get [.index k])
  | .fnRef f types rows => pure (.function f types rows)
  | .method trait m τ => Eval.method D trait m τ
  | .closure ps result ρ body => do
    let captured ← Eval.inspect (memory.capture · (Expr.captures ps body))
    pure (.closure captured ps result ρ body)
  | .call callee args τ => do
    let f ← run callee
    let passed ← Eval.args run args
    call D run f passed τ
  | _ => Eval.fail .stuck

/-- A step of the evaluator of windows, `run` evaluating its parts: on a form that binds, assigns,
chooses, loops, jumps, raises, performs or holds, and on the others as `evalValue`. -/
def evalControl (D : Decls) (run : Expr → Eval (State × World) Value) :
    Expr → Eval (State × World) Value
  | .letIn x τ init body => do
    let v ← run init >>= keep D τ
    Eval.withInit memory x init v (run body)
  | .varIn x τ init body => do
    let v ← run init >>= keep D τ
    Eval.withInit memory x init v (run body)
  | .assign ⟨x, projections⟩ value => Eval.assign memory run x projections value
  | .seq a b => do
    let _ ← run a
    run b
  | .if c _ a b => do
    let v ← run c >>= Eval.asBool
    if v then run a else run b
  | .match e _ arms => do
    let v ← run e >>= resolveE
    Eval.select memory run arms v
  | .for x _ e body => Windows.loop run x e body
  | .raise e => do
    let v ← run e
    Eval.throw v
  | .try e | .form _ e => run e
  | .tryCatch e _ x handler _ =>
    Eval.handle (run e) fun err => do
      let err ← resolveE err
      Eval.withVar memory x err (run handler)
  | .while c body => do
    if ← run c >>= Eval.asBool then
      if ← Eval.turn (run body) then run (.while c body) else pure .unit
    else pure .unit
  | .loop body => do
    if ← Eval.turn (run body) then run (.loop body) else pure .unit
  | .break => Eval.jump .brk
  | .continue => Eval.jump .cont
  | .return e => do
    let v ← run e
    Eval.jump (.ret v)
  | .perform op e => do
    let v ← run e >>= resolveE
    Eval.perform memory op v
  | .withH E c h b => do
    let hv ← run h
    Eval.letGo memory (Eval.handleWith memory E c hv
      (fun f v => callSettled D run c f [.value v] >>= resolveE) (underHandler (run b)))
  | .held names handles body => do
    let hs ← Eval.list run handles
    Eval.held memory (run body) (names.map Prod.fst) hs
  | e => evalValue D run e

end Windows

/-- Evaluates an expression in the model of windows, with at most `fuel` nested steps. Each
case is `eval`'s in `Windows.memory`, but for the views it makes and the windows it reads. -/
def Windows.eval (D : Decls) : Nat → Expr → Eval (Windows.State × World) Value
  | 0, _ => Eval.outOfFuel
  | n + 1, e => Windows.evalControl D (Windows.eval D n) e

/-- An outcome with the value it returns or the error it raises read through its windows, in
the store it ends with: what a run shows of a view is its part. -/
def Outcome.resolveWindows :
    Outcome (Windows.State × World) Value → Outcome (Windows.State × World) Value
  | .done v s => match Windows.resolve s.1.store v with
    | .ok w => .done w s
    | .error f => .fault f s
  | .raised e s => match Windows.resolve s.1.store e with
    | .ok w => .raised w s
    | .error f => .fault f s
  | o => o

/-- Runs `main` with views as windows into their sources' storage, on an input. -/
def Program.runWindows (p : Program) (fuel : Nat) (input : String := "") :
    Outcome (Windows.State × World) Value :=
  ((Windows.eval p.decls fuel p.main (⟨[], []⟩, World.start input)).leaveBody).resolveWindows

end Stilt
