import Stilt.Modes.Copies
import Stilt.Modes.Traverse

/-!
# Uniqueness

The shared writes of a `var` binding or an `inout` parameter `x` (modes.copy-on-write-types, modes.copies and modes.shared-writes), found by walking its scope in source order.

A **copy** of `x` is made where its value, or a part of it with a
copy-on-write type, is bound by a `let`, a `var` or a pattern, assigned to the
whole of another local, captured by a closure literal, stored in a value, or
passed to a consumed parameter of a call after which `x` is used again or to
which it is passed twice (modes.copies). A copy of a copy is a copy of `x`, held by
whatever holds it, so binding, storing or capturing a binding that holds a
part of `x` copies that part again. Each copy lasts until the scope that holds
it ends (`Stilt.Modes.Copies`). A **modification** of `x` (modes.kinds-of-access) is
shared when a copy of the modified part may still last, or when it is inside
a loop whose body, or a `while`'s condition, makes one. An assignment of the whole binding
replaces its value: it is no shared write, and copies made before it, and the
copies of those, no longer count, unless the value assigned holds a part of `x`,
when they count as copies of every part of it.

The walk also finds the writes that `x` makes shared from the other side
(`mirrorsOf`): a modification that reaches inside a copy of a part of `x`
that another binding holds, as its value or at the place of a field, an
element or a part assigned to, which no assignment to that place has
replaced since, while `x`, or another binding holding a copy of an
overlapping part, is used after it, which `later` says of every binding: an `inout`
parameter is used after every point, by the caller its value goes back to. `x`'s scope holds
every use of `x` after the copy, so the walk sees them all. The bindings it
finds are named, so in a scope that binds one name twice both count.

The traversal returns, with the state, the parts of `x` that the value of the
expression holds: they become copies where that value is bound or stored. A
use of `x` after a call is a use of the value passed, so the value assigned to
the whole of `x` is evaluated with no use after it: `xs = grown(xs, i)` gives
up the old value, and its reuse isn't lost. A copy passed to a consumed
parameter lasts as the call's result does, whether or not the binding that
held it is used again. The analysis is lexical and conservative, as the record
asks: a copy counts until its holder's scope ends, whether or not the holder is
used again.
-/

namespace Stilt

/-- Whether an argument uses `x`. -/
def Arg.occurs (x : Name) : Arg → Bool
  | .value e => e.occurs x
  | .inout ⟨y, path⟩ => y == x || pathUse (fun _ _ => false) x path != .none

/-- Whether the indexes of a place use `x`. -/
def pathOccurs (x : Name) (path : List Projection) : Bool :=
  pathUse (fun _ _ => false) x path != .none

/-- Whether `x` is used by any argument of a call but the one at position `n`:
whether a value passed there is passed twice. -/
def otherArgs (x : Name) (args : List Arg) (n : Nat) : Bool :=
  (args.zipIdx.filter (·.2 != n)).any fun (a, _) => a.occurs x

/-- The bindings used after a point, as `later` says, and those that `e` uses. -/
def thenUses (later : Name → Bool) (e : Expr) : Name → Bool := fun y => later y || e.occurs y

/-- The modifications that a call's `inout` arguments make when it starts
(modes.kinds-of-access and modes.durations): of `x`, and of the bindings
holding a copy of a part of it. -/
def Writes.modifyArgs (W : Writes) (later : Name → Bool) (s : Copies) (args : List Arg) :
    Copies :=
  args.foldl (init := s) fun s a =>
    match a with
    | .inout ⟨y, path⟩ =>
      if y == W.x then W.modify s (path.filterMap Projection.fieldName?)
      else W.mirror later s y (path.map Projection.sel) false
    | .value _ => s

/-- Where the walk of `x` meets one of `x`'s own bindings: from there the copies that last
are of that binding's value, so none made before counts, while the bindings that hold parts of
`x` keep them (modes.shared-writes). -/
def Copies.fresh (s : Copies) : Copies := { s with live := [] }

/-- `W` in the scope of a binding of `x` itself, around which no loop has copied its value. -/
def Writes.own (W : Writes) : Writes := { W with loop := [] }

/-- `W` in the scope of a binding `y`: of `x` itself, or of another. -/
def Writes.into (W : Writes) (y : Name) : Writes := if y == W.x then W.own else W

/-- The state in the scope of a binding `y`: of `x` itself, or of another. -/
def Copies.into (W : Writes) (y : Name) (s : Copies) : Copies := if y == W.x then s.fresh else s

/-- A raise or a performance that may leave here, to a `catch` or a `with` around it in the
body: what the analysis knows goes with it. -/
def Writes.escape (W : Writes) (s : Copies) : Copies := if W.catching then s.leave .esc else s

/-- The aliases of `r` that `as` lacks, each widened: at the head of a loop, a binding that a
turn gave a part of `x` may hold any part of it, given a turn before (modes.shared-writes). -/
def Copies.carried (as : List Alias) (r : Copies) : List Alias :=
  ((r.aliases.filter (!as.contains ·)).map fun a =>
    { a with parts := (a.parts.map Part.widen).eraseDups }).eraseDups

/-- The bindings that a turn of a loop at depth `d` may give a part of `x` before it comes to
the head again, from those of `as`: each turn walked from what the head knows, with `fuel`
turns. A turn that adds none reaches the head as it was, and when the turns don't settle, every
binding that the loop assigns, `targets`, may hold any part (modes.shared-writes). -/
def Writes.loopHead (W : Writes) (d : Nat) (targets : List Name) (turn : Writes → Copies → Copies)
    (s : Copies) : Nat → List Alias → List Alias
  | 0, as => as ++ targets.map fun y => ⟨y, s.depthOf y, [Part.whole.bound.widen]⟩
  | fuel + 1, as =>
    let new := Copies.carried as (((turn W { s with aliases := as, pending := [] }).land .cont).close
      (d + 1))
    if new.all as.contains then as else W.loopHead d targets turn s fuel (as ++ new)

/-- A loop at depth `d` whose turn walks with `turn` from the state `s`, and whose body assigns
the bindings `targets`: a modification in it is shared too when a turn makes a copy of an
overlapping part, which a walk of the turn finds, and each turn starts from what the head knows
after any number of turns before (`loopHead`). The loop ends at its head or at a `break`
(modes.shared-writes). -/
def Writes.inLoop (W : Writes) (d : Nat) (targets : List Name) (s : Copies)
    (turn : Writes → Copies → Copies) : Copies :=
  let fuel := 100 * (d + 1) * (s.aliases.length + targets.length + 1)
  let H := { s with aliases := W.loopHead d targets turn s fuel s.aliases, pending := [] }
  let made := (turn W { H with made := [] }).made
  let r := (turn { W with loop := made ++ W.loop } H).land .cont
  let r := { r with live := r.live ++ H.live, aliases := r.aliases ++ H.aliases }.land .brk
  { r with pending := s.pending ++ r.pending }

/-- The bindings that an expression assigns as a whole. -/
def Expr.targets (e : Expr) : List Name :=
  e.gather (fun _ _ _ => ()) (fun _ e => match e with
    | .assign ⟨y, []⟩ _ => [y]
    | _ => []) ()

/-- Walks alternatives with `f` from the state `s`: each from what the analysis knows without
the jumps taken before, which go on once. -/
def Copies.alternatives (s : Copies) (f : Copies → Copies × List Part) : Copies × List Part :=
  let r := f { s with pending := [] }
  ({ r.1 with pending := s.pending ++ r.1.pending }, r.2)

/-- The binding `y`, made at depth `d + 1`, whose value's walk gave `init` and
whose copies the scope at depth `hy` holds, with its scope walked by `body`:
it holds the parts of `x` that value holds, each a copy (modes.copies). A
binding of `x` starts its scope. -/
def Writes.bindIn (W : Writes) (y : Name) (d hy : Nat) (init : Copies × List Part)
    (body : Writes → Copies → Copies × List Part) : Copies × List Part :=
  let s := (W.holdAll hy init.1 init.2).give y (d + 1) (init.2.map Part.bound)
  let r := body ((W.enter y hy).into y) (s.into W y)
  (r.1.close (d + 1), r.2)

/-- The assignment to the place `path` of `y` of a value whose walk gave `r`
(modes.shared-writes and modes.copies). An assignment of the whole of `x` whose value holds a
part of `x` keeps the copies made before it. -/
def Writes.assignOf (W : Writes) (d : Nat) (later : Name → Bool) (y : Name)
    (path : List Projection) (r : Copies × List Part) : Copies × List Part :=
  let sels := path.map Projection.sel
  ((if y == W.x then (if path.isEmpty && !r.2.isEmpty then r.1.reshape else W.assign r.1 path)
    else W.assignTo (if path.isEmpty then r.1 else W.mirror later r.1 y sels true) y path r.2).close
      (d + 1), [])

/-- The handler of a `catch` that binds `y`, walked by `handler` after the
body's walk gave `r`, from what the analysis knows where the body ends and where it raised; the
jumps taken before, `outer`, go on, and so do the body's but its raises. -/
def Writes.catchIn (W : Writes) (y : Name) (d : Nat) (outer : List Pending) (r : Copies × List Part)
    (handler : Writes → Copies → Copies × List Part) : Copies × List Part :=
  let start := { r.1.land .esc with pending := [] }.give y (d + 1) []
  let r' := handler (W.into y) (start.into W y)
  let s' := r'.1.close (d + 1)
  ({ r.1.join s' with pending := outer ++ r.1.pending.filter (·.leave != .esc) ++ s'.pending },
    r.2 ++ r'.2)

/-- A performance's argument, a value that the handler's clause takes and may
give back (handlers.performing-operation): each part of `x` it holds is a copy. -/
def Copies.performed (d : Nat) (r : Copies × List Part) : Copies × List Part :=
  (r.1.close (d + 1), r.2.map (Part.stored none))

/-- A `with` whose handler's walk gave `r`, its block walked by `block`: the
handler's closures hold copies of the parts of `x` it holds (handlers.with). A performance in
the block whose handler doesn't resume ends the `with` (handlers.resuming), so what the analysis
knows there joins what it knows where the block ends; a raise goes on. -/
def Writes.withIn (W : Writes) (d : Nat) (r : Copies × List Part)
    (block : Writes → Copies → Copies × List Part) : Copies × List Part :=
  let s := r.1.close (d + 1)
  let r' := block { W with catching := true } { s with pending := [] }
  let esc := if W.catching then r'.1.pending.filter (·.leave == .esc) else []
  ({ r'.1.land .esc with pending := s.pending ++ (r'.1.land .esc).pending ++ esc },
    r'.2 ++ r.2.map (Part.stored none))

/-- The walks of two alternative branches, joined. -/
def Copies.either (a b : Copies × List Part) : Copies × List Part :=
  (a.1.join b.1, a.2 ++ b.2)

mutual

/-- Walks `e`, at scope depth `d`, whose value the scope at depth `h` holds,
from the state `s`, when `later` says which bindings are used after `e`. Gives
the state after `e`, and the parts of `x` that `e`'s value holds. Each case
follows the order of evaluation of values.left-to-right. -/
def Expr.copies (W : Writes) (d h : Nat) (later : Name → Bool) (s : Copies) :
    Expr → Copies × List Part
  | .var y | .move y => (s, if y == W.x then [Part.whole] else s.partsOf y)
  | .int _ | .bool _ | .unit | .fnRef _ _ _ | .method _ _ _ => (s, [])
  | .break => (s.leave .brk, [])
  | .continue => (s.leave .cont, [])
  | .record _ _ fields => fieldsCopies W d h later s fields
  | .list _ es => exprsCopies W d h later (fun _ => some .elem) 0 s es
  | .op .tuple es => exprsCopies W d h later (fun n => some (.field (tupleField n))) 0 s es
  | .variant _ _ _ es | .op _ es | .view es => exprsCopies W d h later (fun _ => none) 0 s es
  | .field e f => let r := e.copies W d h later s; (r.1, Part.into (some (.field f)) r.2)
  | .index e i =>
    let r := e.copies W d h (thenUses later i) s
    (((i.copies W (d + 1) (d + 1) later r.1).1).close (d + 1), Part.into (some .elem) r.2)
  | .closure ps _ _ body =>
    let parts := W.captured s ps body
    (W.holdAll h s parts, parts.map (Part.stored none))
  | .call f args _ =>
    let r := f.copies W (d + 1) (d + 1) (fun y => later y || args.any (·.occurs y)) s
    let r := argsCopies W (d + 1) h later (fun n => later W.x || otherArgs W.x args n)
      (consumesArg W.consumed f) 0 r.1 args
    (W.escape ((W.modifyArgs later r.1 args).close (d + 1)), r.2.map (Part.stored none))
  | .letIn y τ init body | .varIn y τ init body =>
    let hy := W.scopeOf (d + 1) h y τ body
    W.bindIn y d hy (init.copies W (d + 1) hy (fun z => later z || (y != z && body.occurs z)) s)
      fun W s => body.copies W (d + 1) h later s
  | .assign ⟨y, path⟩ v =>
    let s := (pathCopies W (d + 1) (fun z => later z || y == z || v.occurs z) s path).close (d + 1)
    W.assignOf d later y path (v.copies W (d + 1) (if y == W.x then d + 1 else W.holderOf y)
      (fun z => if z == y then !path.isEmpty else later z) s)
  | .seq a b =>
    let r := a.copies W (d + 1) (d + 1) (thenUses later b) s
    b.copies W d h later (r.1.close (d + 1))
  | .if c _ a b =>
    let s := (c.copies W (d + 1) (d + 1) (fun z => later z || a.occurs z || b.occurs z) s).1
    (s.close (d + 1)).alternatives fun s =>
      Copies.either (a.copies W d h later s) (b.copies W d h later s)
  | .match e _ arms =>
    let r := e.copies W (d + 1) (d + 1) (fun z => later z || armsOccur z arms) s
    let ra := (W.holdAll (d + 1) r.1 r.2).alternatives fun s => armsCopies W (d + 1) h later r.2 s arms
    (ra.1.close (d + 1), ra.2)
  | .for y _ e body =>
    let again := thenUses later body
    let r := e.copies W (d + 1) (d + 1) again s
    let elems := Part.into (some .elem) r.2
    let s := (W.holdAll (d + 1) r.1 elems).give y (d + 1) (elems.map Part.bound)
    ((W.inLoop (d + 1) body.targets s fun W s =>
      (body.copies (W.into y) (d + 2) (d + 2) again (s.into W y)).1).close (d + 1), [])
  | .try e | .form _ e => e.copies W d h later s
  | .tryCatch e _ y hd _ =>
    W.catchIn y d s.pending (e.copies { W with catching := true } d h
      (fun z => later z || (y != z && hd.occurs z)) { s with pending := [] })
      fun W s => hd.copies W (d + 1) h later s
  | .while c body =>
    let again := fun z => later z || c.occurs z || body.occurs z
    ((W.inLoop d (c.targets ++ body.targets) s fun W s =>
      let s := (c.copies W (d + 1) (d + 1) again s).1.close (d + 1)
      (body.copies W (d + 1) (d + 1) again s).1).close (d + 1), [])
  | .loop body => ((W.inLoop d body.targets s fun W s =>
      (body.copies W (d + 1) (d + 1) (thenUses later body) s).1).close (d + 1), [])
  | .raise e => (W.escape (e.copies W d 0 later s).1, [])
  | .return e => ((e.copies W d 0 later s).1, [])
  | .perform _ e =>
    let r := Copies.performed d (e.copies W (d + 1) (d + 1) later s)
    (W.escape r.1, r.2)
  | .withH _ _ hd b =>
    W.withIn d (hd.copies W (d + 1) (d + 1) (thenUses later b) s) fun W s => b.copies W d h later s
  | .held ns hs body =>
    let s := (exprsCopies W (d + 1) (d + 1) (thenUses later body) (fun _ => none) 0 s hs).1.close (d + 1)
    if ns.any (·.1 == W.x) then body.copies W.own d h later s.fresh else body.copies W d h later s

/-- Walks expressions whose values are stored in a value, which the scope at
depth `h` holds, from the one at position `n`: each part of `x` they hold is a
copy (modes.copies), which the value holds inside, at the place `step` leads
to from the position, if it has one: a tuple's field or a list's element. -/
def exprsCopies (W : Writes) (d h : Nat) (later : Name → Bool) (step : Nat → Option Sel)
    (n : Nat) (s : Copies) : List Expr → Copies × List Part
  | [] => (s, [])
  | e :: es =>
    let r := e.copies W d h (fun y => later y || es.any (·.occurs y)) s
    let rs := exprsCopies W d h later step (n + 1) (W.holdAll h r.1 r.2) es
    (rs.1, r.2.map (Part.stored (step n)) ++ rs.2)

/-- Walks the fields of a record literal, which store their values in it. -/
def fieldsCopies (W : Writes) (d h : Nat) (later : Name → Bool) (s : Copies) :
    List (Name × Expr) → Copies × List Part
  | [] => (s, [])
  | (f, e) :: fields =>
    let r := e.copies W d h (fun y => later y || fields.any (·.2.occurs y)) s
    let rs := fieldsCopies W d h later (W.holdAll h r.1 r.2) fields
    (rs.1, r.2.map (Part.stored (some (.field f))) ++ rs.2)

/-- Walks a call's arguments, at the call's depth `d`, from position `n`, and
gives the parts that the call's result may hold. What an argument to a
consumed parameter holds lasts as the call's result does, at depth `h`, and so
does a part it passes that is a copy already, or a part of `x` whose reuse
`lost n` says is lost; what any other argument holds lasts for the call
(modes.copies). -/
def argsCopies (W : Writes) (d h : Nat) (later : Name → Bool) (lost consumed : Nat → Bool)
    (n : Nat) (s : Copies) : List Arg → Copies × List Part
  | [] => (s, [])
  | .value e :: args =>
    let r := e.copies W d (if consumed n then h else d)
      (fun y => later y || args.any (·.occurs y)) s
    let kept := if consumed n then r.2.filter fun p => lost n || p.copied else []
    let rs := argsCopies W d h later lost consumed (n + 1) (W.holdAll h r.1 kept) args
    (rs.1, kept ++ rs.2)
  | .inout ⟨_, path⟩ :: args =>
    argsCopies W d h later lost consumed (n + 1)
      (pathCopies W d (fun y => later y || args.any (·.occurs y)) s path) args

/-- Walks the indexes of a place, whose values the scope at depth `d` holds. -/
def pathCopies (W : Writes) (d : Nat) (later : Name → Bool) (s : Copies) :
    List Projection → Copies
  | [] => s
  | .field _ :: path => pathCopies W d later s path
  | .index i :: path =>
    pathCopies W d later ((i.copies W d d (fun y => later y || pathOccurs y path) s).1) path

/-- Walks the arms of a `match`, each from the same state, since one of them
runs. An arm's binders, in the scope at depth `d`, hold copies of the parts
of `x` that the scrutinee holds, `parts`, at the places of it they match
(modes.copies); an arm that binds `x` hides it. -/
def armsCopies (W : Writes) (d h : Nat) (later : Name → Bool) (parts : List Part) (s : Copies) :
    List Arm → Copies × List Part
  | [] => (s, [])
  | ⟨pattern, binders, guard, body⟩ :: arms =>
    let s' := binders.foldl (fun s b => s.give b d (pattern.partsAt b parts)) s
    let later' := fun z => later z || body.occurs z || armsOccur z arms
    if binders.contains W.x then
      Copies.either (body.copies W.own d h later (guardCopies W.own d later' s'.fresh guard))
        (armsCopies W d h later parts s arms)
    else
      let sg := guardCopies W d later' s' guard
      Copies.either (body.copies W d h later sg) (armsCopies W d h later parts sg arms)

/-- Walks an arm's guard, a condition, which the arm's body or the next arms follow; the
next arms start from the state after it, with the arm's copies still counted. -/
def guardCopies (W : Writes) (d : Nat) (later : Name → Bool) (s : Copies) : Option Expr → Copies
  | none => s
  | some g => (g.copies W (d + 1) (d + 1) later s).1.close (d + 1)

end

/-- The walk of a binding `x` of type `τ` in the body `body` that makes it, from the body's start:
a binding of `x` starts its scope, and after the scope ends the walk goes on, since the bindings
outside it may hold copies of its parts. The `inout` parameters `inouts` are used after it, when
their values go back to the caller (modes.shared-writes). -/
def walk (D : Decls) (C : Consumed) (inouts : List Name) (x : Name) (τ : Ty) (body : Expr) :
    Copies :=
  (body.copies ⟨D, C, inouts, x, τ, [], [], false⟩ 1 0 inouts.contains ⟨[], [], false, [], [], []⟩).1

/-- The bindings that a body makes, outside its closure literals, which are bodies of their own:
each with its type, when the core gives one (a `match` arm's binders carry none), and whether
it may be modified, as a `var` may (modes.shared-writes). -/
def Expr.bodyBinders (body : Expr) : List (Name × Option Ty × Bool) :=
  body.gather (fun inside e _ => inside || e.isClosure) (fun inside e =>
    if inside then [] else match e with
    | .letIn y τ _ _ | .for y τ _ _ | .tryCatch _ τ y _ _ => [(y, some τ, false)]
    | .varIn y τ _ _ => [(y, some τ, true)]
    | .held ns _ _ => ns.map fun (y, τ) => (y, some τ, false)
    | .match _ _ arms => arms.flatMap fun a => a.binders.map fun y => (y, none, false)
    | _ => []) false

end Stilt
