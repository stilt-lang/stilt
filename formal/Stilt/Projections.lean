import Stilt.Free
import Stilt.Syntax.Forms

/-!
# Projections

A projection, `fn f(…) -> inout T { body }` (projections.declaring-projection), is a form of
the calculus, which it writes as the calls it means. The caller's access to a projection's call,
what the caller does with the place the call is (projections.call-is-place), is a closure literal
that takes the yielded place `inout`, and the projection is a function of its own for each type
of access, whose last parameter takes the access: `Expr.projectionBody` is its body, whose
`yield p` calls the access with `p` `inout` (`Expr.yieldOf`) and keeps the access's value, which
the body ends with and its `return` gives (`Expr.yieldedOf`), and `Expr.projectCall` is a call of
it from the caller, with the access as its last argument. The projection's arguments are
evaluated first, as a call's are; its call then runs its body to its `yield`, where the access
happens on the yielded place in the caller's code, resumes after it and writes its `inout`
arguments back when it ends (projections.when-projection-runs). The access runs in the caller,
with the caller's effects: one that raises, or performs an operation whose handler ends it,
leaves the projection as a raise or a performance leaves any call, so the statements after its
`yield` don't run, no `catch` of the projection's sees the error, and its `inout` arguments are
written back holding what was written before the `yield` and through the place
(projections.raising-during-access and handlers.ended-projections, `Outcome.leaveCall`). A
handler's body reaches no place of the calls it ends: the operation's argument is a value and
its captures copies, and the rest after the performance goes on from the frames the performance
left (handlers.when-place-is-seen, `Outcome`).

`Program.Projections` checks the rules of projections on that syntax
(`Program.projectionsChecked`):

* every path through a projection's body from its start to its end or to a `return` runs
  exactly one `yield`, and one that ends by raising or panicking at most one; a `yield` inside a
  loop, a guard or the operand of a `catch` is E0424 (projections.once-on-every-path,
  `Expr.once`);
* a `yield` and the value it keeps are only in the body of a projection, and in no closure
  literal (projections.yield, E0425), and a `return` in that body takes no value;
* a projection's body raises nothing of its own: no `raise` and no call marked by a `try`
  outside the operand of a `catch`, as its row holds no `raise` (projections.cannot-raise,
  E0427); what it raises is its access's;
* a projection is named only as the callee of a call where a place is
  (projections.not-a-value, E0426), and no closure literal is one
  (projections.declaring-projection).
-/

namespace Stilt

/-- The body of a projection written for an access whose value has type `R`, from the body
`b` it was declared with: `var res: List<R> = []`, then `b`, which adds the access's value to
`res` at its `yield`, and then the value kept, `res[0]` (projections.declaring-projection and
projections.yield). -/
def Expr.projectionBody (res : Name) (R : Ty) (b : Expr) : Expr :=
  .form .projection (.varIn res (.list R) (.list R []) (.seq b (.index (.var res) (.int 0))))

/-- `yield p` in a projection's body, whose access, its last parameter `k`, takes the yielded
place and the places the access threads, `places`, `inout`, and whose value of type `R` is
added to `res` (projections.yield and projections.when-projection-runs). The place's indexes
are evaluated when the statement runs, and the access then happens on it. -/
def Expr.yieldOf (res k : Name) (R : Ty) (places : List Place) : Expr :=
  .form .yield (.assign ⟨res, []⟩
    (.op (.list .push) [.var res, .try (.call (.var k) (places.map .inout) R)]))

/-- The value a projection's body ends with, which its `return` gives: the access's
(projections.yield: a `return` in the body takes no value). -/
def Expr.yieldedOf (res : Name) : Expr := .form .yielded (.index (.var res) (.int 0))

/-- A call of the projection `f` where a place is, at its type arguments and rows, with its
arguments and, last, the caller's access, a closure literal that takes the yielded place
`inout`, of type `R` (projections.call-is-place and projections.when-projection-runs). -/
def Expr.projectCall (f : Name) (types : List Ty) (rows : List Row) (args : List Arg) (R : Ty) :
    Expr :=
  .form .project (.call (.fnRef f types rows) args R)

/-! ## Paths through a projection's body -/

/-- What the paths through code leave of the `yield`s a projection's body runs: `none` when
the code breaks a rule of projections, `some none` when no path through it ends normally, and
`some (some n)` when every path that does has run `n`. -/
abbrev Yields := Option (Option Nat)

/-- The paths after `r`, each going on with `f` from the `yield`s it has run. -/
def Yields.andThen : Yields → (Nat → Yields) → Yields
  | none, _ => none
  | some none, _ => some none
  | some (some n), f => f n

/-- The paths of two branches, one of which runs: those that end normally agree. -/
def Yields.join : Yields → Yields → Yields
  | some none, r => r
  | r, some none => r
  | some (some m), some (some n) => if m = n then some (some m) else none
  | _, _ => none

/-- Code that runs no `yield`, on any path: every path that ends normally has run `n`. -/
def Yields.keeps (n : Nat) (r : Yields) : Bool := r == some (some n) || r == some none

mutual

/-- Whether `e` holds a form of projections other than a call of one: a projection's body,
a `yield` or the value it keeps. -/
def Expr.yields : Expr → Bool
  | .var _ | .move _ | .int _ | .bool _ | .unit | .break | .continue | .fnRef .. | .method .. => false
  | .form k e => (k.ofProjection && k != .project) || e.yields
  | .record _ _ fields => fieldsYield fields
  | .variant _ _ _ es | .list _ es | .op _ es | .view es => exprsYield es
  | .field e _ | .raise e | .try e | .return e | .loop e | .perform _ e => e.yields
  | .index a b | .seq a b | .while a b | .withH _ _ a b | .letIn _ _ a b | .varIn _ _ a b
  | .for _ _ a b | .tryCatch a _ _ b _ => a.yields || b.yields
  | .closure _ _ _ body => body.yields
  | .call callee args _ => callee.yields || argsYield args
  | .assign ⟨_, path⟩ value => pathYields path || value.yields
  | .if c _ a b => c.yields || a.yields || b.yields
  | .match e _ arms => e.yields || armsYield arms
  | .held _ hs body => exprsYield hs || body.yields

def exprsYield : List Expr → Bool
  | [] => false
  | e :: es => e.yields || exprsYield es

def fieldsYield : List (Name × Expr) → Bool
  | [] => false
  | (_, e) :: fields => e.yields || fieldsYield fields

def argsYield : List Arg → Bool
  | [] => false
  | .value e :: args => e.yields || argsYield args
  | .inout ⟨_, path⟩ :: args => pathYields path || argsYield args

def pathYields : List Projection → Bool
  | [] => false
  | .field _ :: path => pathYields path
  | .index i :: path => i.yields || pathYields path

def armsYield : List Arm → Bool
  | [] => false
  | ⟨_, _, guard, body⟩ :: arms => guardYields guard || body.yields || armsYield arms

def guardYields : Option Expr → Bool
  | none => false
  | some g => g.yields

end

end Stilt
