import Stilt.Generics.Commute
import Stilt.Typing.Par

/-!
# Tasks, scopes and lazy values

The forms of `std.task`, `std.lazy` and `std.par` (`Stilt.Typing.Par`) as `Expr.form` keeps them, each with the code it means
in the sequential run, which gives a program with tasks its one meaning
(tasks.sequential-run), and the rules that typing asks of each beside that code's
(`TaskForm`, read by `HasType.task`). A task's handle, a scope and a lazy value are records of
the library, which the export declares as the calculus writes them: `Task<T>` holds the value
its task ended with, `Scope<E>` holds nothing, and `Lazy<T>` holds its function. Their names are
no name a program's declaration can have, and the calculus has no `?` type, so nothing else
reaches their fields.

`async` is no label of the calculus's rows: in the sequential run it performs nothing but what
its tasks' calls do, so the export writes a row that holds it as one that holds `io`, as it does
a row that holds an effect, and a `with` of one of its handlers is its block's run.
-/

namespace Stilt

/-- The name the export gives `std.task`'s `Task<T>`. -/
def taskName : Name := "std.task.Task"

/-- The name the export gives `std.task`'s `Scope<E>`. -/
def scopeName : Name := "std.task.Scope"

/-- The name the export gives `std.lazy`'s `Lazy<T>`. -/
def lazyName : Name := "std.lazy.Lazy"

/-- `T` names `Task<T>`, declared as a record of one type parameter with one field, `value`, the
value the task ended with. -/
def Decls.IsTask (D : Decls) (T : Name) : Prop :=
  T = taskName ∧ ∃ r p, D.record? T = some r ∧ r.typeParams = [p] ∧ r.fields = [("value", .param p)]

/-- `S` names `Scope<E>`, declared as a record of one type parameter, the error type of its
tasks, with no field. -/
def Decls.IsScope (D : Decls) (S : Name) : Prop :=
  S = scopeName ∧ ∃ r p, D.record? S = some r ∧ r.typeParams = [p] ∧ r.fields = []

/-- `L` names `Lazy<T>`, declared as a record of one type parameter with one field, `get`, the
function it keeps, whose row is empty (polymorphism.lazy-values). -/
def Decls.IsLazy (D : Decls) (L : Name) : Prop :=
  L = lazyName ∧ ∃ r p, D.record? L = some r ∧ r.typeParams = [p] ∧
    r.fields = [("get", .fn [] (.param p) Row.pure)]

/-- A row a task's function may have (tasks.task-functions): `io`, and at most a `raise<E>`,
which only a task of a scope has; no row variable, no user-defined effect and no `resume`.
`async` holds `io` in the calculus's rows. -/
def Row.OfTask (ρ : Row) : Prop := ρ.vars = [] ∧ ρ.effects = [] ∧ ρ.resume = none

/-- A task's handle once its function, bound to `g`, has run to its end: the record of the value
it ended with. -/
def Expr.taskOf (T : Name) (τ : Ty) (g : Name) : Expr :=
  .record T [τ] [("value", .call (.var g) [] τ)]

/-- `task.spawn(f)` at the result type `τ`: `f` bound to `g` at its type, then called with no
arguments, to its end, its value the task's handle. -/
def Expr.spawnOf (T g : Name) (ρ : Row) (f : Expr) (τ : Ty) : Expr :=
  .form .spawn (.letIn g (.fn [] τ ρ) f (Expr.taskOf T τ g))

/-- `t.await()`, the task's handle bound to `h`, and its value read. -/
def Expr.awaitOf (T h : Name) (τ : Ty) (t : Expr) : Expr :=
  .form .await (.letIn h (.record T [τ]) t (.field (.var h) "value"))

/-- `task.scope(f)` at the result type `τ`: `f` called with a new scope of the error type `E`. -/
def Expr.scopeOf (S : Name) (E : Ty) (f : Expr) (τ : Ty) : Expr :=
  .form .scope (.call f [.value (.record S [E] [])] τ)

/-- `s.spawn(f)` at the result type `τ`: the scope bound to `r`, then the task run as
`task.spawn(f)` runs it. -/
def Expr.scopeSpawnOf (S r : Name) (E : Ty) (s : Expr) (T g : Name) (ρ : Row) (f : Expr)
    (τ : Ty) : Expr :=
  .form .scopeSpawn (.letIn r (.record S [E]) s (.letIn g (.fn [] τ ρ) f (Expr.taskOf T τ g)))

/-- `with h { b }` for a handler `h` of `async`: `h`, then the block. -/
def Expr.asyncWith (h b : Expr) : Expr := .form .async (.seq h b)

/-- `Lazy.new(f)`: the lazy value that keeps `f`. -/
def Expr.lazyNewOf (L : Name) (τ : Ty) (f : Expr) : Expr :=
  .form .lazyNew (.record L [τ] [("get", f)])

/-- `l.get()`: the lazy value bound to `h`, and its function called. -/
def Expr.lazyGetOf (L h : Name) (τ : Ty) (l : Expr) : Expr :=
  .form .lazyGet (.letIn h (.record L [τ]) l (.call (.field (.var h) "get") [] τ))

/-- The rules of the forms of tasks, scopes and lazy values beside those of the code each means,
which `HasType.task` types: `TaskForm D k m τ` says that `m` is the code the form `k` means, of
the type `τ`, as its rules shape it. -/
inductive TaskForm (D : Decls) : Form → Expr → Ty → Prop
  /-- tasks.std-task, tasks.task-functions and tasks.sequential-run: `spawn(f)` gives a
  `Task<T>`, of a function that takes nothing and gives a `T`, whose row holds `io` at most: it
  raises nothing and performs no user-defined effect. In the sequential run, `spawn` runs the
  task's function to its end before it returns: the code binds `f`, calls it, and its value is
  the task's handle. The call is one through a stored function value, so a site of `div`
  (tasks.implicit-effects-and-capabilities, `Expr.divFree`), and the body of a closure literal
  given to it adds its own sites where it is written. The form asks no `io` of its own; the
  export writes `async`, through which the Reference reaches the capability `spawn`, as `io`, so
  that capability is left out, with the allocation of the task (the record of its value allocates
  nothing) and E0502 at the closure literal, which typing gives as a row that doesn't fit. That
  the function is `portable` is `Program.Demands`' (shared.tasks-and-modes, E0432). -/
  | spawn {T g ρ f τ} : D.IsTask T → ρ.OfTask → ρ.raise = none →
      TaskForm D .spawn (.letIn g (.fn [] τ ρ) f (Expr.taskOf T τ g)) (.record T [τ])
  /-- tasks.std-task and tasks.sequential-run: `t.await()` takes a `Task<T>` and gives the value
  the task ended with, as often as it is called: its handle holds it. -/
  | await {T h τ t} : D.IsTask T →
      TaskForm D .await (.letIn h (.record T [τ]) t (.field (.var h) "value")) τ
  /-- tasks.scopes: `task.scope(f)` runs `f` with a new scope of tasks that may raise `E`, and
  ends once every task started in it has ended, which in the sequential run is once `f` has,
  each task having run to its end where it was started. `f`'s row passes on as a call's does,
  `raise<E>` among it. -/
  | scope {S E f τ} : D.IsScope S →
      TaskForm D .scope (.call f [.value (.record S [E] [])] τ) τ
  /-- tasks.scopes and tasks.scope-failure: `s.spawn(f)` takes a scope and gives a `Task<U>` of
  a function whose row holds `io` and at most a `raise<E>`. In the sequential run it runs the task
  to its end, and a task that raises raises at `s.spawn`: the call is one of the code, so typing
  asks `try` of it (effects.marking), and the raise leaves the scope as any raise does, unless the
  scope's function catches it. The calculus's rows aren't substituted by types, so the rule
  doesn't tie the row's error type to the scope's; the export writes both as the program does. -/
  | scopeSpawn {S r E s T g ρ f τ} : D.IsScope S → D.IsTask T → ρ.OfTask →
      TaskForm D .scopeSpawn
        (.letIn r (.record S [E]) s (.letIn g (.fn [] τ ρ) f (Expr.taskOf T τ g))) (.record T [τ])
  /-- tasks.with-waits: a `with` of an `async` handler ends once every task started under it has
  ended. In the sequential run, each has ended where it was started, so the `with` is its block's
  run. The model leaves out the rule that a dropped handle is no unused value: a statement of
  the calculus has type `()`. -/
  | async {h b τ} : TaskForm D .async (.seq h b) τ
  /-- polymorphism.lazy-values: `Lazy.new(f)` takes a function that takes nothing and whose row
  is empty, which the field of `Lazy<T>` asks `f` to fit, so a function that performs `io` or
  raises doesn't fit (E0502). -/
  | lazyNew {L τ f} : D.IsLazy L →
      TaskForm D .lazyNew (.record L [τ] [("get", f)]) (.record L [τ])
  /-- polymorphism.lazy-values: `l.get()` gives the value of the function `l` keeps, at its
  type. The model calls the function at each `get`, where the Reference computes the value once,
  at the first, and keeps it for every copy: it states less than that rule, a difference the
  Reference makes no program able to observe, of which `lazy_unobservable` proves a part.
  polymorphism.lazy-implicit-effects: the call is one through a stored function value, so a site
  of `div` (`Expr.divFree`), and it adds none of the function's `panic` or `div`, which count
  where its closure literal is written or its function named; the allocation of `new` and `get`
  is left out (the record of the function allocates nothing). -/
  | lazyGet {L h τ l} : D.IsLazy L →
      TaskForm D .lazyGet (.letIn h (.record L [τ]) l (.call (.field (.var h) "get") [] τ)) τ
  /-- par.std-par and par.sequential-meaning: `par.map(xs, f)` takes a `List<T>` and a function
  of type `fn(T) -> U`, and gives the `List<U>` of `f` of each element, in order: the code binds
  the list, then the function, then calls it on the elements from the first to the last, pushing
  each value. par.what-runs-in-parallel: the function's type has an empty row, so a closure
  literal whose body prints or raises doesn't fit it (E0502), nor a named function whose row
  isn't empty (E0311); that it is `calm` and `portable` is `Program.ParDemands`' (E0431). The
  parameter is `escaping`, which the model writes as that row alone; the allocation of the native
  is left out. -/
  | parMap {n g acc x T U xs f} :
      TaskForm D .parMap (.letIn n (.list T) xs (.letIn g (Ty.parMapFn T U) f
        (.varIn acc (.list U) (.list U [])
          (.seq (.for x T (.var n) (.assign ⟨acc, []⟩
            (.op (.list .push) [.var acc, .call (.var g) [.value (.var x)] U]))) (.var acc)))))
        (.list U)
  /-- par.std-par, par.sequential-meaning and par.writes-in-place: `par.each(inout xs, f)` takes
  a list at a place `P` and a function of type `fn(inout T)`, with an empty row, and calls it on
  each element of the list in place, from the first index to the last: each call takes the place
  `P[i]` `inout`, so it writes that element and no other, into the storage of `xs` in the model
  of in-place mutation. The model has the form for a place of fields alone, `P` read once for its
  length; the parallel run of `view.split`'s parts with `par.both` is the run of two calls that
  take writable bindings, which the model doesn't state apart. -/
  | parEach {g i T f} {P : Place} : (∀ q ∈ P.path, q.IndexedBy []) →
      TaskForm D .parEach (.letIn g (Ty.parEachFn T) f
        (.for i .i64 (.op (.list (.range false)) [.int 0, .op (.list .len) [P.read]])
          (.call (.var g) [.inout ⟨P.root, P.path ++ [.index (.var i)]⟩] .unit))) .unit
  /-- par.std-par and par.sequential-meaning: `par.both(f, g)` takes two functions that take
  nothing, with empty rows, and gives the pair of their values: the code binds `f`, then `g`, then
  calls `f`, then `g`. -/
  | parBoth {a b A B f g} :
      TaskForm D .parBoth (.letIn a (.fn [] A Row.pure) f (.letIn b (.fn [] B Row.pure) g
        (.op .tuple [.call (.var a) [] A, .call (.var b) [] B]))) (.tuple [A, B])
  /-- par.std-par and par.fold-tree: `par.fold(xs, empty, f)` takes a `List<T>`, a `T` and a
  function of type `fn(T, T) -> T`, with an empty row, binds them in order, gives `empty` for an
  empty list, and otherwise calls the function the program declares as `FnDecl.foldTree`: a list
  of one element is itself, and a longer one of `n` elements its first `n / 2` folded, combined
  by `f` with the rest folded, a tree that depends on `n` alone. The two halves are folded one
  after the other, the left first, the order par.panics reports in. -/
  | parFold {n d g T xs e f} : D.fn? foldTreeName = some FnDecl.foldTree →
      TaskForm D .parFold (.letIn n (.list T) xs (.letIn d T e (.letIn g (Ty.parFoldFn T) f
        (.if (.op (.compare .eq .i64) [.op (.list .len) [.var n], .int 0]) T (.var d)
          (Expr.foldTreeCall T (.var n) (.var g)))))) T

/-- A task's row keeps its shape once its type parameters are replaced, which leaves rows as
they are. -/
theorem TaskForm.substTys {D : Decls} (s : TySubst) :
    ∀ {k : Form} {m : Expr} {τ : Ty}, TaskForm D k m τ → TaskForm D k (m.substTys s) (τ.substTys s)
  | _, _, _, .spawn hT hρ hr => .spawn hT hρ hr
  | _, _, _, .await hT => .await hT
  | _, _, _, .scope hS => .scope hS
  | _, _, _, .scopeSpawn hS hT hρ => .scopeSpawn hS hT hρ
  | _, _, _, .async => .async
  | _, _, _, .lazyNew hL => .lazyNew hL
  | _, _, _, .lazyGet hL => .lazyGet hL
  | _, _, _, .parMap => .parMap
  | _, _, _, @TaskForm.parEach _ g i T f ⟨x, path⟩ hP => by
    have hr := Expr.readPath_substTys s [] path (.var x) hP
    have hp := substPathTys_indexed s [] path hP
    have hi : substPathTys s (path ++ [.index (.var i)]) = path ++ [.index (.var i)] :=
      substPathTys_indexed s [i] _ fun q hq => by
        rcases List.mem_append.1 hq with hq | hq
        · rcases hP q hq with h | ⟨t, ht, _⟩
          · exact .inl h
          · cases ht
        · rcases List.mem_singleton.1 hq with rfl
          exact .inr ⟨i, List.mem_singleton_self _, rfl⟩
    simp only [Expr.substTys, substExprTys, substArgTys, Place.read, Ty.parEachFn, Ty.substTys,
      substParamTys, Op.substTys] at hr ⊢
    rw [hr, hi]
    exact .parEach hP
  | _, _, _, .parBoth => .parBoth
  | _, _, _, .parFold hF => .parFold hF

end Stilt
