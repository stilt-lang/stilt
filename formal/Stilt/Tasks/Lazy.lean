import Stilt.Locks.Theorem
import Stilt.Typing.Tasks

/-!
# A lazy value's function waits for nothing

polymorphism.lazy-waits-for-nothing: a site of `locks` (shared.locks) in the closure literal or
function given to `Lazy.new`, or in the closure literal that a `let` binds to the local given to
it, is E0435. `Expr.lazyFns` gathers those functions as the program writes them, at any depth,
closure literals' bodies included, and `Program.LazyLocks` asks each to hold no site of `locks`
(`Expr.lockFree`), which for a function named is that it hasn't the fact.

What the check is for follows from `eval_takesNone`: the call of such a function, from a frame
whose function values are lock-free, holds no cell in any state it reaches that the world it
started in didn't, and neither does the rest of a performance (`Program.LazyLocks.call`). So the
function never waits on a shared value, and never on the code that asked for its value. The
Reference also makes a `when` that runs while the function runs panic with the kind `deadlock`,
one reached through a function value included, which no check sees; the calculus computes a lazy
value at each `get`, as a call (`TaskForm.lazyGet`), so that panic is left out, and the export
declines a program with a lazy value and a `when`.
-/

namespace Stilt

/-- The closure literals that `let` binds, by name, the latest first. -/
abbrev LetClosures := List (Name × Expr)

/-- The closure literals that `C` binds, but those of the names `xs`, which a binder hides
(expressions.shadowing). -/
def LetClosures.hide (C : LetClosures) (xs : List Name) : LetClosures :=
  C.filter fun p => !xs.contains p.1

/-- The closure literals once `x` is bound to `init`: `init` when it is one, and `x` hidden. -/
def LetClosures.bind (C : LetClosures) (x : Name) : Expr → LetClosures
  | .closure ps r ρ body => (x, .closure ps r ρ body) :: C.hide [x]
  | _ => C.hide [x]

/-- The function given to `Lazy.new` as the check reads it: the closure literal that a `let`
bound to the local given, or what is given. -/
def LetClosures.fn (C : LetClosures) : Expr → Expr
  | .var x | .move x => (C.lookup x).getD (.var x)
  | f => f

/-- The function that the record of a lazy value keeps, read through `C`. -/
def LetClosures.kept (C : LetClosures) : Expr → List Expr
  | .record _ _ [("get", f)] => [C.fn f]
  | _ => []

mutual

/-- The functions given to `Lazy.new` in `e`, at any depth, closure literals' bodies included,
each read through the closure literals `C` that `let`s bind. -/
def Expr.lazyFns (C : LetClosures) : Expr → List Expr
  | .var _ | .move _ | .int _ | .bool _ | .unit | .break | .continue | .fnRef _ _ _
  | .method _ _ _ => []
  | .closure ps _ _ body => body.lazyFns (C.hide (ps.map Param.name))
  | .record _ _ fields => fieldsLazyFns C fields
  | .variant _ _ _ es | .list _ es | .op _ es | .view es => exprsLazyFns C es
  | .form k e => (if k = .lazyNew then C.kept e else []) ++ e.lazyFns C
  | .field e _ | .raise e | .try e | .return e | .loop e | .perform _ e => e.lazyFns C
  | .index a b | .seq a b | .while a b | .withH _ _ a b => a.lazyFns C ++ b.lazyFns C
  | .letIn x _ init body => init.lazyFns C ++ body.lazyFns (C.bind x init)
  | .varIn x _ init body | .for x _ init body => init.lazyFns C ++ body.lazyFns (C.hide [x])
  | .tryCatch e _ x h _ => e.lazyFns C ++ h.lazyFns (C.hide [x])
  | .held ns hs body => exprsLazyFns C hs ++ body.lazyFns (C.hide (ns.map (·.1)))
  | .call callee args _ => callee.lazyFns C ++ argsLazyFns C args
  | .assign ⟨_, path⟩ value => pathLazyFns C path ++ value.lazyFns C
  | .if c _ a b => c.lazyFns C ++ a.lazyFns C ++ b.lazyFns C
  | .match e _ arms => e.lazyFns C ++ armsLazyFns C arms
  termination_by structural e => e

def exprsLazyFns (C : LetClosures) : List Expr → List Expr
  | [] => []
  | e :: es => e.lazyFns C ++ exprsLazyFns C es
  termination_by structural es => es

def fieldsLazyFns (C : LetClosures) : List (Name × Expr) → List Expr
  | [] => []
  | (_, e) :: fields => e.lazyFns C ++ fieldsLazyFns C fields
  termination_by structural fields => fields

def argsLazyFns (C : LetClosures) : List Arg → List Expr
  | [] => []
  | .value e :: args => e.lazyFns C ++ argsLazyFns C args
  | .inout ⟨_, path⟩ :: args => pathLazyFns C path ++ argsLazyFns C args
  termination_by structural args => args

def pathLazyFns (C : LetClosures) : List Projection → List Expr
  | [] => []
  | .field _ :: path => pathLazyFns C path
  | .index i :: path => i.lazyFns C ++ pathLazyFns C path
  termination_by structural path => path

def armsLazyFns (C : LetClosures) : List Arm → List Expr
  | [] => []
  | ⟨_, binders, guard, body⟩ :: arms =>
    guardLazyFns (C.hide binders) guard ++ body.lazyFns (C.hide binders) ++ armsLazyFns C arms
  termination_by structural arms => arms

def guardLazyFns (C : LetClosures) : Option Expr → List Expr
  | none => []
  | some g => g.lazyFns C
  termination_by structural g => g

end

/-- The functions given to `Lazy.new` in every body of a program, and in `main`. -/
def Program.lazyFns (p : Program) : List Expr :=
  p.decls.fns.flatMap (·.body.lazyFns []) ++ p.main.lazyFns []

/-- E0435 (polymorphism.lazy-waits-for-nothing): no function given to `Lazy.new`, as written or
as the closure literal that a `let` binds to the local given, holds a site of `locks`: a `when`,
or a use of a function that has the fact. -/
def Program.LazyLocks (p : Program) : Prop :=
  ∀ f ∈ p.lazyFns, f.lockFree p.decls p.decls.locks = true

/-- polymorphism.lazy-waits-for-nothing: whatever the order of write-back, the call of a function
given to `Lazy.new`, as written or instantiated, from a frame whose function values are lock-free,
holds no cell in any state it reaches that its world didn't hold when it started, and neither does
the rest of a performance, from the world it is resumed in. So it never waits on a shared value,
nor on the code that asked for its value. Of the paragraph, the panic of a `when` that runs while
the function does, through a function value, is left out: the calculus calls the function at each
`get`. -/
theorem Program.LazyLocks.call {p : Program} (hp : p.LazyLocks) (w : WriteBack) (n : Nat)
    {f : Expr} (hf : f ∈ p.lazyFns) (τ : Ty) (ts : TySubst) (rs : RowSubst) {s : Copy.State}
    (hs : Frame.LockFree p.decls p.decls.locks s.1) :
    (eval p.decls (Copy.memoryWith w) n (((Expr.call f [] τ).substTys ts).substRows rs) s).TakesNone
      p.decls p.decls.locks (Value.LockFree p.decls p.decls.locks) s.2 :=
  eval_takesNone p.decls.locks_closed w n _
    (by
      rw [Expr.lockFree_substRows, Expr.lockFree_substTys]
      simp [Expr.lockFree, argsLockFree, hp f hf]) s hs

end Stilt
