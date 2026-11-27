import Stilt.Run.Decode
import Stilt.Semantics
import Stilt.Windows.Eval
import Stilt.Sharing.Eval

/-!
# Running an exported program

A program read from JSON (`Stilt.Run.Decode`), run on its input in the models of memory of
copies, of in-place mutation, of windows when it makes a view and of sharing when it may share,
and what the run shows as a process would: its standard output, its exit status and what it
writes to standard error (program.exit-statuses).

Printing and reading are operations on the world (std.io), which every model of
memory carries beside its frames: the world a run ends in holds what it wrote,
however it ends, so a raise that escapes `main` and a panic show what was written
before them (effects.panic-kinds and program.exit-statuses).
The calculus has no source locations, so the report of a panic names no place.
-/

namespace Stilt.Run

open Lean (Json)

def typeParam : Decoder TypeParam
  | .arr #[n, bs] => return ⟨← str n, ← list str bs, []⟩
  | j => throw s!"a type parameter, not {j.compress}"

/-- Limits: an array of their names, `"panic"`, `"overflow"` and `"div"` (facts.without). -/
def limits (j : Json) : Except String Limits := do
  (← list str j).foldlM (init := {}) fun l n => match n with
    | "panic" => pure { l with panic := true }
    | "overflow" => pure { l with overflow := true }
    | "div" => pure { l with div := true }
    | _ => throw s!"a limit, not {n}"

/-- A function: `[name, typeParams, rowParams, params, result, row, body]`, and after
them the limits its body keeps, none when they are left out. -/
def fnDecl (j : Json) : Except String FnDecl :=
  match j with
  | .arr #[n, tps, rps, ps, r, rw, b] => decode n tps rps ps r rw b (.arr #[])
  | .arr #[n, tps, rps, ps, r, rw, b, ls] => decode n tps rps ps r rw b ls
  | j => throw s!"a function, not {j.compress}"
where
  decode (n tps rps ps r rw b ls : Json) : Except String FnDecl := do
    return ⟨← str n, ← list typeParam tps, ← list str rps, ← list param ps, ← ty r, ← row rw,
      ← expr b, ← limits ls⟩

def head (j : Json) : Except String Head := do
  match (← ty j).head? with
  | some h => pure h
  | none => throw s!"no impl is for the type {j.compress}"

/-- The declarations: an object of their lists, the effects' and the constants' optional. -/
def decls (j : Json) : Except String Decls := do
  let get (k : String) : Except String Json := j.getObjVal? k
  return {
    records := ← get "records" >>= list (fun r => match r with
      | .arr #[n, fs, ps] => return ⟨← str n, ← list (pair str ty) fs, ← list str ps⟩
      | _ => do
        let (n, fs) ← pair str (list (pair str ty)) r
        pure ⟨n, fs, []⟩)
    variants := ← get "variants" >>= list (fun v => match v with
      | .arr #[n, cs, ps] => return ⟨← str n, ← list (pair str (list ty)) cs, ← list str ps⟩
      | _ => do
        let (n, cs) ← pair str (list (pair str (list ty))) v
        pure ⟨n, cs, []⟩)
    functions := ← get "functions" >>= list fnDecl
    impls := ← get "impls" >>= list (fun i => do
      let (t, fs) ← pair str (list fnDecl) i
      pure ⟨t, fs, []⟩)
    traits := ← get "traits" >>= list (fun t => do
      let (n, ms) ← pair str (list (pair str ty)) t
      pure ⟨n, ms, []⟩)
    traitImpls := ← get "traitImpls" >>= list (fun i => match i with
      | .arr #[t, h, fs] => return ⟨← str t, ← head h, ← list fnDecl fs, [], []⟩
      | _ => throw s!"a trait impl, not {i.compress}")
    effects := ← (j.getObjVal? "effects").toOption.getD (.arr #[]) |> list (fun e => do
      let (n, ops) ← pair str (list (pair str (pair ty ty))) e
      pure ⟨n, ops⟩)
    consts := ← (j.getObjVal? "consts").toOption.getD (.arr #[]) |> list (fun c => match c with
      | .arr #[n, t, v] => return ⟨← str n, ← ty t, ← expr v⟩
      | _ => throw s!"a constant, not {c.compress}") }

/-- A program: an object of its declarations, `main`, `main`'s row and, when given,
the limits `main`'s body keeps. -/
def program (j : Json) : Except String Program := do
  return ⟨← j.getObjVal? "decls" >>= decls, ← j.getObjVal? "main" >>= expr,
    ← j.getObjVal? "row" >>= row, ← (j.getObjVal? "limits").toOption.getD (.arr #[]) |> limits⟩

/-- What a process shows of a run. -/
structure Shown where
  stdout : String
  stderr : String
  status : UInt32
  deriving BEq, Repr

/-- Why the model gives no run: a program or a run it declines, as an
implementation of part of the language does, or one it fails on. -/
inductive Problem where
  | declines (why : String)
  | fails (why : String)

/-- The text `error: {e}` shows of a raised value whose `Show` the model has. -/
def shownError : Value → Option String
  | .str s => some s
  | .int n => some (toString n)
  | .bool b => some (toString b)
  | _ => none

def _root_.Stilt.PanicKind.name : PanicKind → String
  | .bounds => "bounds"
  | .overflow => "overflow"
  | .divideByZero => "divide-by-zero"
  | .utf8Boundary => "utf8-boundary"
  | .missingKey => "missing-key"
  | .explicit => "explicit"
  | .unreachable => "unreachable"
  | .unwrap => "unwrap"
  | .assert => "assert"
  | .deadlock => "deadlock"
  | .checkError => "check-error"

/-- What a panic writes to standard error: its kind, then where it happened,
which the model can't tell (program.exit-statuses). -/
def panicReport (k : PanicKind) : String :=
  s!"panic: {k.name}: the model keeps no message\n  at no place: the model has no source locations\n"

/-- What a run shows: the output and standard error of the world it ends in, and for a
raise that escapes `main` and a panic, their report after them, with status 1 and 101
(program.exit-statuses). -/
def shown {σ : Type} : Outcome (σ × World) Value → Except Problem Shown
  | .done _ s => pure ⟨s.2.out, s.2.err, 0⟩
  | .raised e s => match shownError e with
    | some m => pure ⟨s.2.out, s.2.err ++ s!"error: {m}\n", 1⟩
    | none => throw (.declines "a raise escaped main with a value whose `Show` the model lacks")
  | .jumped _ _ => throw (.fails "a `break`, `continue` or `return` escaped main's body")
  | .panicked k s => pure ⟨s.2.out, s.2.err ++ panicReport k, 101⟩
  | .performed .. => throw (.fails "a performance escaped main")
  | .outOfFuel => throw (.declines "a run nested deeper than the model's fuel")
  | .stuck => throw (.fails "the run got stuck")

mutual

/-- Whether an expression makes a view (views.making-view). -/
def _root_.Stilt.Expr.makesView : Expr → Bool
  | .view _ => true
  | .var _ | .move _ | .int _ | .bool _ | .unit | .break | .continue | .fnRef .. | .method .. =>
    false
  | .record _ _ fields => fieldsMakeView fields
  | .variant _ _ _ es | .list _ es | .op _ es => exprsMakeView es
  | .field e _ | .raise e | .try e | .form _ e | .return e | .loop e | .perform _ e => e.makesView
  | .index a b | .seq a b | .while a b | .withH _ _ a b | .letIn _ _ a b | .varIn _ _ a b
  | .for _ _ a b | .tryCatch a _ _ b _ => a.makesView || b.makesView
  | .closure _ _ _ body => body.makesView
  | .call callee args _ => callee.makesView || argsMakeView args
  | .assign ⟨_, path⟩ value => pathMakesView path || value.makesView
  | .if c _ a b => c.makesView || a.makesView || b.makesView
  | .match e _ arms => e.makesView || armsMakeView arms
  | .held _ hs body => exprsMakeView hs || body.makesView

/-- Whether an expression of the list makes a view. -/
def exprsMakeView : List Expr → Bool
  | [] => false
  | e :: es => e.makesView || exprsMakeView es

/-- Whether a field of a record literal makes a view. -/
def fieldsMakeView : List (Name × Expr) → Bool
  | [] => false
  | (_, e) :: fields => e.makesView || fieldsMakeView fields

/-- Whether an argument, or an index of an `inout` one, makes a view. -/
def argsMakeView : List Arg → Bool
  | [] => false
  | .value e :: args => e.makesView || argsMakeView args
  | .inout ⟨_, path⟩ :: args => pathMakesView path || argsMakeView args

/-- Whether an index of a place makes a view. -/
def pathMakesView : List Projection → Bool
  | [] => false
  | .field _ :: path => pathMakesView path
  | .index i :: path => i.makesView || pathMakesView path

/-- Whether an arm makes a view. -/
def armsMakeView : List Arm → Bool
  | [] => false
  | ⟨_, _, guard, body⟩ :: arms => guardMakesView guard || body.makesView || armsMakeView arms

/-- Whether an arm's guard makes a view. -/
def guardMakesView : Option Expr → Bool
  | none => false
  | some g => g.makesView

end

/-- Whether a program makes a view, in `main` or a function. -/
def _root_.Stilt.Program.makesView (p : Program) : Bool :=
  p.main.makesView || p.decls.functions.any (·.body.makesView) ||
    p.decls.impls.any (·.fns.any (·.body.makesView)) ||
    p.decls.traitImpls.any (·.fns.any (·.body.makesView))

/-- What an expression does that may tell sharing from in-place mutation: the names that a
binding of a place, or an assignment of one to the whole of a binding, may make share storage
(`.inl`), the binding and the place's root, and the roots of the places it modifies or passes
`inout` (`.inr`). -/
def _root_.Stilt.Expr.sharingSites (e : Expr) : List (Name ⊕ Name) :=
  e.gather (fun _ _ _ => ()) (fun _ e => match e with
    | .letIn y _ init _ | .varIn y _ init _ | .assign ⟨y, []⟩ init =>
      match init.place? with
      | some p => [.inl y, .inl p.root]
      | none => []
    | .assign ⟨y, _ :: _⟩ _ => [.inr y]
    | .call _ args _ => args.filterMap fun
      | .inout p => some (.inr p.root)
      | .value _ => none
    | _ => []) ()

/-- Whether a program may tell sharing from in-place mutation: it modifies a place, or passes
one `inout`, whose root has a name that a binding of a place may make share storage. In any
other program no binding that shares storage, or whose storage another shares, is modified,
so the model of sharing is in-place mutation. -/
def _root_.Stilt.Program.shares (p : Program) : Bool :=
  let sites := p.main.sharingSites ++ p.decls.fns.flatMap (·.body.sharingSites)
  let sharing := sites.filterMap fun | .inl y => some y | .inr _ => none
  sites.any fun | .inr y => sharing.contains y | .inl _ => false

/-- Runs a program on its input in the models of memory, which must show the same: copies,
in-place mutation, windows when the program makes a view, and sharing when it may share: in a
program that makes no view, the model of windows is in-place mutation, and so is the model of
sharing in one that doesn't share. -/
def run (p : Program) (input : String) (fuel : Nat) : Except Problem Shown := do
  let copy ← shown (p.runCopy fuel input)
  let agrees (o : Except Problem Shown) : Bool := match o with
    | .ok s => s == copy
    | .error _ => false
  if !agrees (shown (p.runInPlace fuel input)) then
    throw (.fails "copies and in-place mutation disagree")
  if p.makesView && !agrees (shown (p.runWindows fuel input)) then
    throw (.fails "copies and windows disagree")
  if p.shares && !agrees (shown (p.runSharing fuel input)) then
    throw (.fails "copies and sharing disagree")
  pure copy

end Stilt.Run
