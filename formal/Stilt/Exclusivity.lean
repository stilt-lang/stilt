import Stilt.Places

/-!
# Exclusivity

The law of exclusivity (modes.kinds-of-access, modes.law and modes.durations), as one syntactic pass over a
body, like the reference interpreter's.

Mutability (modes.what-can-be-modified) is part of typing, in `Stilt.Typing`: a modification of
what can't be modified is a type error, and a well-typed program needs only
this pass besides.
-/

namespace Stilt

/-- The places that the `for` loops around a binding of `x` read, as seen
inside it. The binding hides the outer `x`, so no access to the outer `x` can
begin in its scope. The reference interpreter gets the same effect by giving each variable
its own identity. -/
def hide (reading : List Shape) (x : Name) : List Shape :=
  reading.filter (·.root != x)

/-- A modification of a place with shape `s` doesn't overlap any place that a
loop around it reads (modes.change-while-iterating, E0404). -/
def unread (reading : List Shape) (s : Shape) : Bool :=
  !reading.any s.overlaps

/-- No two places of the list overlap (modes.overlapping-inout, E0402). -/
def pairwiseDisjoint : List Shape → Bool
  | [] => true
  | s :: ss => ss.all (fun t => !s.overlaps t) && pairwiseDisjoint ss

/-- The places that a call's `inout` arguments modify, in order. A method
call passes its receiver as its first argument, so the receiver of an `inout
self` method comes first (traits.qualified-calls; modes.durations). -/
def inoutShapes : List Arg → List Shape
  | [] => []
  | .inout p :: args => p.shape :: inoutShapes args
  | .value _ :: args => inoutShapes args

/-- The place a `for` loop reads for the whole of its body, if its iterable is
a place (modes.durations). -/
def iterated (e : Expr) : List Shape :=
  (e.place?.map Place.shape).toList

mutual

/-- Whether `e` obeys the law of exclusivity (modes.law) while the `for`
loops around it, in its body, read the places `reading`.

Under the durations of modes.durations, only two kinds of access are still in progress
when another begins: the read of a `for` loop's place, which lasts for its
whole body, and the modifications of a call's `inout` arguments, which begin
together when the call starts and last until it returns, while the caller
does nothing else. Every other access ends before the next one begins. So the
law comes down to the two violations of modes.overlapping-inout and modes.change-while-iterating, which this checks: a
modification of a place that overlaps one a loop around it reads (E0404), and
two overlapping `inout` arguments of one call, the receiver of an `inout self`
method among them (E0402).

A closure captures by copy and can't modify what it captures (modes.closures), so its
body starts with no place being read. -/
def Expr.exclusive (reading : List Shape) : Expr → Bool
  | .var _ | .move _ | .int _ | .bool _ | .unit | .break | .continue | .fnRef _ _ _ | .method _ _ _ => true
  | .record _ fields => fieldsExclusive reading fields
  | .variant _ _ es => exprsExclusive reading es
  | .list _ es => exprsExclusive reading es
  | .op _ es | .view es => exprsExclusive reading es
  | .field e _ => e.exclusive reading
  | .index e i => e.exclusive reading && i.exclusive reading
  | .closure _ _ _ body => body.exclusive []
  | .call callee args _ =>
    callee.exclusive reading && argsExclusive reading args &&
      (inoutShapes args).all (unread reading) && pairwiseDisjoint (inoutShapes args)
  | .letIn x _ init body => init.exclusive reading && body.exclusive (hide reading x)
  | .varIn x _ init body => init.exclusive reading && body.exclusive (hide reading x)
  | .assign ⟨root, path⟩ value =>
    pathExclusive reading path && value.exclusive reading &&
      unread reading (Place.mk root path).shape
  | .seq a b => a.exclusive reading && b.exclusive reading
  | .if c _ a b => c.exclusive reading && a.exclusive reading && b.exclusive reading
  | .match e _ arms => e.exclusive reading && armsExclusive reading arms
  | .for x _ e body => e.exclusive reading && body.exclusive (hide (iterated e ++ reading) x)
  | .raise e => e.exclusive reading
  | .try e => e.exclusive reading
  | .tryCatch e _ x handler _ => e.exclusive reading && handler.exclusive (hide reading x)
  | .while c body => c.exclusive reading && body.exclusive reading
  | .loop body => body.exclusive reading
  | .return e => e.exclusive reading
  | .perform _ e => e.exclusive reading
  | .withH _ _ h b => h.exclusive reading && b.exclusive reading
  | .held ns hs body =>
    exprsExclusive reading hs && body.exclusive ((ns.map Prod.fst).foldl hide reading)

/-- Whether every expression of a list obeys the law. -/
def exprsExclusive (reading : List Shape) : List Expr → Bool
  | [] => true
  | e :: es => e.exclusive reading && exprsExclusive reading es

/-- Whether every field of a record literal obeys the law. -/
def fieldsExclusive (reading : List Shape) : List (Name × Expr) → Bool
  | [] => true
  | (_, e) :: fields => e.exclusive reading && fieldsExclusive reading fields

/-- Whether the arguments of a call obey the law while they are evaluated:
the value of each argument, and the indexes of each `inout` place. -/
def argsExclusive (reading : List Shape) : List Arg → Bool
  | [] => true
  | .value e :: args => e.exclusive reading && argsExclusive reading args
  | .inout ⟨_, path⟩ :: args => pathExclusive reading path && argsExclusive reading args

/-- Whether the indexes of a place obey the law. -/
def pathExclusive (reading : List Shape) : List Projection → Bool
  | [] => true
  | .field _ :: path => pathExclusive reading path
  | .index i :: path => i.exclusive reading && pathExclusive reading path

/-- Whether the arms of a `match` obey the law. Each binder of an arm hides
the variable of the same name. -/
def armsExclusive (reading : List Shape) : List Arm → Bool
  | [] => true
  | ⟨_, binders, body⟩ :: arms =>
    body.exclusive (binders.foldl hide reading) && armsExclusive reading arms

end

/-- Every body of the program obeys the law of exclusivity: each function's
body, and `main`. -/
def Program.Exclusive (p : Program) : Prop :=
  (∀ d ∈ p.decls.fns, d.body.exclusive [] = true) ∧ p.main.exclusive [] = true

/-! ## Lemmas -/

/-- A loop reading a place forbids modifying it, and any place that overlaps
it (modes.change-while-iterating). -/
theorem unread_iff (reading : List Shape) (s : Shape) :
    unread reading s = true ↔ ∀ t ∈ reading, s.overlaps t = false := by
  simp [unread]

/-- The `inout` arguments of a call keep the law together exactly when no two
of them overlap (modes.overlapping-inout). -/
theorem pairwiseDisjoint_iff (ss : List Shape) :
    pairwiseDisjoint ss = true ↔ ss.Pairwise (fun s t => s.overlaps t = false) := by
  induction ss with
  | nil => simp [pairwiseDisjoint]
  | cons s ss ih => simp [pairwiseDisjoint, ih]

/-! ## The required tests of modes.law -/

section RequiredTests

private def place (x : Name) (path : List Projection := []) : Place := ⟨x, path⟩

private def call (f : Name) (args : List Arg) : Expr := .call (.var f) args .unit

/-- `xs[0]`, as an expression. -/
private def first (xs : Name) : Expr := .index (.var xs) (.int 0)

/-- `swap(inout a, inout a)` is rejected. -/
example : (call "swap" [.inout (place "a"), .inout (place "a")]).exclusive [] = false := by
  decide

/-- `f(inout a.b, inout a)` is rejected. -/
example :
    (call "f" [.inout (place "a" [.field "b"]), .inout (place "a")]).exclusive [] = false := by
  decide

/-- `swap(inout xs[0], inout xs[1])` is rejected: indexes are removed before
places are compared. -/
example :
    (call "swap" [.inout (place "xs" [.index (.int 0)]),
      .inout (place "xs" [.index (.int 1)])]).exclusive [] = false := by
  decide

/-- `f(inout a.b, inout a.c)` is accepted. -/
example :
    (call "f" [.inout (place "a" [.field "b"]),
      .inout (place "a" [.field "c"])]).exclusive [] = true := by
  decide

/-- `f(inout a, a)` is accepted: the second argument is read before the call
starts. -/
example : (call "f" [.inout (place "a"), .value (.var "a")]).exclusive [] = true := by
  decide

/-- `push(inout xs, xs[0])`, the shape of `xs.push(xs[0])`, is accepted. -/
example : (call "push" [.inout (place "xs"), .value (first "xs")]).exclusive [] = true := by
  decide

/-- `for x in xs { xs[0] = x }` is rejected (E0404). -/
example :
    (Expr.for "x" .i64 (.var "xs")
      (.assign (place "xs" [.index (.int 0)]) (.var "x"))).exclusive [] = false := by
  decide

/-- `for x in xs { f(inout xs) }` is rejected (E0404). -/
example :
    (Expr.for "x" .i64 (.var "xs") (call "f" [.inout (place "xs")])).exclusive [] = false := by
  decide

/-- `for item in cart.items { remove(inout cart, item) }` is rejected (E0404):
`cart` contains the iterated place. -/
example :
    (Expr.for "item" .i64 (.field (.var "cart") "items")
      (call "remove" [.inout (place "cart"), .value (.var "item")])).exclusive [] = false := by
  decide

/-- Reading the iterated place inside the loop is accepted. -/
example :
    (Expr.for "x" .i64 (.var "xs")
      (.assign (place "total") (first "xs"))).exclusive [] = true := by
  decide

/-- Modifying a different list inside the loop is accepted. -/
example :
    (Expr.for "x" .i64 (.var "xs")
      (.assign (place "ys" [.index (.int 0)]) (.var "x"))).exclusive [] = true := by
  decide

/-- Iterating a value that isn't a place, such as `enumerate(xs)`, while
modifying `xs` is accepted. -/
example :
    (Expr.for "x" .i64 (call "enumerate" [.value (.var "xs")])
      (.assign (place "xs" [.index (.int 0)]) (.var "x"))).exclusive [] = true := by
  decide

/-- A new `xs` inside the loop hides the iterated one, so modifying it is
accepted. -/
example :
    (Expr.for "x" .i64 (.var "xs")
      (.varIn "xs" (.list .i64) (.list .i64 [.int 0])
        (.assign (place "xs" [.index (.int 0)]) (.var "x")))).exclusive [] = true := by
  decide

end RequiredTests

end Stilt
