import Stilt.Alloc.Sites
import Stilt.Sharing.Names
import Stilt.Moves.Marking
import Stilt.Rows.Types

/-!
# Own storage and writes in place

Where a binding holds its own storage (facts.own-storage), which writes through an index are in
place (facts.writes-in-place), which parameters are in place (facts.in-place-parameters), and
which arguments a call copies for an in-place parameter (facts.copy-at-call).

The walk goes through a body in the order of evaluation with, for each binding in scope, its
type and whether it holds its own storage there (`Own`). A parameter of a function limited by
`without alloc` holds it where the body starts; a `let` or `var` holds it when its initializer is
a list literal or names whole, at its last use, a binding that holds it; an assignment of the
whole binding gives it storage of its own or takes it away the same way. A binding that a
pattern, a `for`, a `catch`, a `when` or a closure literal's parameters bind holds none. Where
paths meet, after an `if` or a `match`, a binding holds its storage when it does on each path;
inside a loop, and after it, a binding holds it when it did before the loop and no assignment of
it in the loop gives it anything but a list literal, which covers the assignments of later turns
(`Expr.staleWrites`). The last uses are those that `Expr.markMoves` marks (facts.last-use), so the
walk reads a body with its marks.

The walk fails at a write through an index that isn't in place, and at an `inout` argument
through an index, when it checks `writes`; in both modes, at an argument that a call copies for
an in-place parameter, unless it is a list literal, names whole at its last use a binding that
holds its own storage, or, for an `inout` parameter, names whole such a binding whose
modifications aren't shared. The model departs from the Reference in three ways, each stricter:
a modification is shared when the inference calls its binding shared at any of its
modifications (`ModeEnv.allShared`, modes.shared-writes); a parameter is in place when the body
writes it through an index, passes it whole to an in-place parameter, or hands its storage on at
a last use, whether or not the storage reaches a write in place (`Expr.feedsInPlace`); and the
assignments of a loop that give a list literal count as giving storage only on the turn that
makes them.

These are checks of acceptance alone: the model proves no run-time promise of them, that a write
in place copies nothing or that an in-place parameter gets storage no other value shares, since
its values share no storage.
-/

namespace Stilt

/-- The bindings in scope, the newest first, each with its type and whether it holds its own storage
(facts.own-storage). A check of acceptance alone: the model proves no run-time promise of it, since
its values share no storage. -/
abbrev Own := List (Name × Ty × Bool)

namespace Own

/-- The type of the newest binding of `x`, when it holds its own storage. -/
def owns (O : Own) (x : Name) : Option Ty :=
  match O.find? (·.1 == x) with
  | some (_, τ, true) => some τ
  | _ => none

/-- The newest binding of `x` holding its own storage or not, as `b` says. -/
def set (x : Name) (b : Bool) : Own → Own
  | [] => []
  | (y, τ, c) :: O => if y == x then (y, τ, b) :: O else (y, τ, c) :: set x b O

/-- Where two paths meet: a binding holds its storage when it does on both. -/
def meet (O O' : Own) : Own := List.zipWith (fun (y, τ, b) (_, _, b') => (y, τ, b && b')) O O'

/-- The bindings `xs` holding no storage of their own. -/
def lose (xs : List Name) (O : Own) : Own := xs.foldl (fun O x => O.set x false) O

/-- No binding holding storage of its own. -/
def disown (O : Own) : Own := O.map fun (y, τ, _) => (y, τ, false)

/-- New bindings that hold no storage of their own: a pattern's, a `for`'s, a `catch`'s or a
`when`'s, whose types the walk doesn't need. -/
def bindNone (xs : List Name) (O : Own) : Own := xs.map (fun x => (x, Ty.unit, false)) ++ O

/-- Whether a value gives the binding it is assigned to storage of its own: a list literal, or a binding
named whole at its last use that holds its own storage (facts.own-storage). A check of acceptance
alone: the model proves no run-time promise of it, since its values share no storage. -/
def gives (O : Own) : Expr → Bool
  | .list _ _ => true
  | .move y => (O.owns y).isSome
  | _ => false

end Own

/-- The bindings that an assignment of the whole in `e` may give storage that isn't their own: one that
assigns anything but a list literal (facts.own-storage). A check of acceptance alone: the model
proves no run-time promise of it, since its values share no storage. -/
def Expr.staleWrites (e : Expr) : List Name :=
  e.gather (fun _ _ _ => ()) (fun _ e => match e with
    | .assign ⟨_, []⟩ (.list _ _) => []
    | .assign ⟨x, []⟩ _ => [x]
    | _ => []) ()

/-- The function a call names, if it names one: a function, or a trait method whose impl is known where
the call is written (facts.in-place-parameters and facts.inference). A check of acceptance alone:
the model proves no run-time promise of it, since its values share no storage. -/
def Decls.calleeName? (D : Decls) : Expr → Option Name
  | .fnRef g _ _ => some g
  | .method t m τ => τ.head?.bind fun h => (D.traitImpl? t h).map fun _ => implName t h m
  | _ => none

/-- Whether an argument names the binding `p` whole. -/
def Arg.namesWhole (p : Name) : Arg → Bool
  | .value (.var y) | .value (.move y) => y == p
  | .inout ⟨y, []⟩ => y == p
  | _ => false

section

variable (D : Decls) (IP : Name → Nat → Bool)

/-- Whether a call of `g` passes `p` whole, from position `k` on, to an in-place parameter. -/
def passesTo (g p : Name) : Nat → List Arg → Bool
  | _, [] => false
  | k, a :: args => (IP g k && a.namesWhole p) || passesTo g p (k + 1) args

/-- Whether the storage of `p` may reach a write in place in `e` (facts.in-place-parameters): `e` writes
`p` through an index, passes it whole to an in-place parameter of a callee it names, or hands its
storage on at a last use, to a binding that may write it in place. A check of acceptance alone: the
model proves no run-time promise of it, since its values share no storage. -/
def Expr.feedsInPlace (p : Name) (e : Expr) : Bool :=
  (e.gather (fun _ _ _ => ()) (fun _ e => match e with
    | .move y => [y == p]
    | .assign ⟨y, path⟩ _ => [y == p && !Place.indexFree ⟨y, path⟩]
    | .call f args _ => match D.calleeName? f with
      | some g => [passesTo IP g p 0 args]
      | none => []
    | _ => []) ()).any id

/-- The in-place parameters, `IP name k` for the parameter at position `k` of the function `name`
(facts.in-place-parameters): a parameter of a function limited by `without alloc` whose storage may
reach a write in place is in place, and a parameter of any other function, or of a native function,
never is. The Reference solves recursive groups as a fixed point from no parameter in place; every
set closed this way holds that one, and a call copies for a parameter only when the set holds it, so
the least is the one that adds fewest sites, and a check that some closed set passes is a check that
the least one does. The marks of last uses are those of `FnDecl.markMoves`. A check of acceptance
alone: the model proves no run-time promise of it, since its values share no storage. -/
def Decls.InPlaceParams : Prop :=
  (∀ name k, IP name k = true → ∃ d, D.fn? name = some d ∧ d.limits.alloc = true) ∧
  ∀ d ∈ D.fns, d.limits.alloc = true → ∀ k q, d.params[k]? = some q →
    d.markMoves.body.feedsInPlace D IP q.name = true → IP d.name k = true

end

section

-- `sh` holds the bindings of the body whose modifications are shared (modes.shared-writes), and
-- `writes` says whether writes through an index are checked, as `without alloc` checks them.
variable (D : Decls) (sh : List Name) (IP : Name → Nat → Bool) (writes : Bool)

/-- Whether a write to a place is in place, or goes through no index (facts.writes-in-place): the place
is `b[i]`, of a binding `b` of type `List<T>` that holds its own storage there, whose modifications
aren't shared, or goes on from it through fields when `T` isn't a copy-on-write type and holds no
type parameter (modes.copy-on-write-types). A check of acceptance alone: the model proves no
run-time promise of it, since its values share no storage. -/
def Own.inPlace (O : Own) (p : Place) : Bool :=
  p.indexFree ||
    (!sh.contains p.root && match O.owns p.root, p.path with
      | some (.list T), .index _ :: rest =>
        Place.indexFree ⟨p.root, rest⟩ && (rest.isEmpty || (!D.cow T && T.params.isEmpty))
      | _, _ => false)

/-- Whether an argument passed to an in-place parameter is copied there (facts.copy-at-call): unless it
is a list literal, or names whole at its last use a binding that holds its own storage, or is an
`inout` argument naming whole such a binding whose modifications aren't shared. An `inout` argument
through an index already allocates, and adds nothing here. A check of acceptance alone: the model
proves no run-time promise of it, since its values share no storage. -/
def Own.copies (O : Own) : Arg → Bool
  | .value e => !O.gives e
  | .inout ⟨y, []⟩ => (O.owns y).isNone || sh.contains y
  | .inout p => p.indexFree

/-- Whether a call of `g` copies an argument, from position `k` on, for an in-place parameter. -/
def Own.copiesAt (O : Own) (g : Name) : Nat → List Arg → Bool
  | _, [] => false
  | k, a :: args => (IP g k && Own.copies sh O a) || Own.copiesAt O g (k + 1) args

/-- Whether a call of `f` copies an argument for an in-place parameter of the function it names. -/
def Own.callCopies (O : Own) (f : Expr) (args : List Arg) : Bool :=
  match D.calleeName? f with
  | some g => Own.copiesAt sh IP O g 0 args
  | none => false

mutual

/-- The walk of `e` from the bindings `O`: the bindings after it, or `none` at a write through an index
that isn't in place or an `inout` argument through an index, when `writes`, and at an argument
copied for an in-place parameter (facts.own-storage, facts.writes-in-place and facts.copy-at-call).
A check of acceptance alone: the model proves no run-time promise of it, since its values share no
storage. -/
def Expr.storesIn : Own → Expr → Option Own
  | O, .var _ | O, .move _ | O, .int _ | O, .bool _ | O, .unit | O, .break | O, .continue
  | O, .fnRef _ _ _ | O, .method _ _ _ => some O
  | O, .record _ _ fields => fieldsStores O fields
  | O, .variant _ _ _ es | O, .list _ es | O, .op _ es | O, .view es => exprsStores O es
  | O, .field e _ | O, .raise e | O, .try e | O, .form _ e | O, .return e | O, .perform _ e =>
    e.storesIn O
  | O, .index a b | O, .seq a b => do
    let O ← a.storesIn O
    b.storesIn O
  | O, .closure ps _ _ body => do
    let _ ← body.storesIn (ps.map (fun q => (q.name, q.type, false)) ++ O.disown)
    pure O
  | O, .call f args _ => do
    let O ← f.storesIn O
    let O' ← argsStores O args
    if Own.callCopies D sh IP O f args then none else pure O'
  | O, .letIn x τ init body | O, .varIn x τ init body => do
    let O ← init.storesIn O
    let O' ← body.storesIn ((x, τ, O.gives init) :: O)
    pure O'.tail
  | O, .assign ⟨x, path⟩ v => do
    let O ← pathStores O path
    let O ← v.storesIn O
    if path.isEmpty then pure (O.set x (O.gives v))
    else if !writes || Own.inPlace D sh O ⟨x, path⟩ then pure O else none
  | O, .if c _ a b => do
    let O ← c.storesIn O
    let A ← a.storesIn O
    let B ← b.storesIn O
    pure (A.meet B)
  | O, .match e _ arms => do
    let O ← e.storesIn O
    armsStores O arms
  | O, .for x τ e body => do
    let O ← e.storesIn O
    let O := O.lose body.staleWrites
    let _ ← body.storesIn ((x, τ, false) :: O)
    pure O
  | O, .while c body => do
    let O ← c.storesIn (O.lose (c.staleWrites ++ body.staleWrites))
    let _ ← body.storesIn O
    pure O
  | O, .loop body => do
    let O := O.lose body.staleWrites
    let _ ← body.storesIn O
    pure O
  | O, .tryCatch e _ x h _ => do
    let A ← e.storesIn O
    let H ← h.storesIn (Own.bindNone [x] (O.lose e.staleWrites))
    pure (A.meet H.tail)
  | O, .withH _ _ h b => do
    let O ← h.storesIn O
    let B ← b.storesIn O
    pure (B.meet (O.lose b.staleWrites))
  | O, .held ns hs body => do
    let O ← exprsStores O hs
    let B ← body.storesIn (Own.bindNone (ns.map Prod.fst) O)
    pure (B.drop ns.length)

/-- The walk of a list of expressions, in order. -/
def exprsStores : Own → List Expr → Option Own
  | O, [] => some O
  | O, e :: es => do
    let O ← e.storesIn O
    exprsStores O es

/-- The walk of the fields of a record literal, in order. -/
def fieldsStores : Own → List (Name × Expr) → Option Own
  | O, [] => some O
  | O, (_, e) :: fields => do
    let O ← e.storesIn O
    fieldsStores O fields

/-- The walk of a call's arguments, in order: an `inout` argument through an index allocates
(facts.allocation). -/
def argsStores : Own → List Arg → Option Own
  | O, [] => some O
  | O, .value e :: args => do
    let O ← e.storesIn O
    argsStores O args
  | O, .inout ⟨y, path⟩ :: args => do
    let O ← pathStores O path
    if writes && !Place.indexFree ⟨y, path⟩ then none else argsStores O args

/-- The walk of the indexes of a place, in order. -/
def pathStores : Own → List Projection → Option Own
  | O, [] => some O
  | O, .field _ :: path => pathStores O path
  | O, .index i :: path => do
    let O ← i.storesIn O
    pathStores O path

/-- The walk of the arms of a `match`: each arm's binders hold no storage of their own, and the
arms meet after the `match`. -/
def armsStores : Own → List Arm → Option Own
  | O, [] => some O
  | O, ⟨_, binders, guard, body⟩ :: arms => do
    let G ← guardStores (Own.bindNone binders O) guard
    let A ← body.storesIn G
    let R ← armsStores O arms
    pure (Own.meet (A.drop binders.length) R)

/-- The walk of an arm's guard. -/
def guardStores : Own → Option Expr → Option Own
  | O, none => some O
  | O, some g => g.storesIn O

end

end

/-- The facts that the inference of modes.shared-writes reads, of declarations. -/
def Decls.modeEnv (D : Decls) : ModeEnv := ⟨D, D.consumed, D.onceParams⟩

/-- The bindings where a function's body starts: its parameters, each holding its own storage when the
function is limited by `without alloc` (facts.own-storage). A check of acceptance alone: the model
proves no run-time promise of it, since its values share no storage. -/
def FnDecl.ownAtStart (d : FnDecl) : Own := d.params.map fun q => (q.name, q.type, d.limits.alloc)

/-- Whether the walk of a function's body, with its last uses marked, passes: when `writes`,
every write through an index is in place, and in both modes no argument is copied for an
in-place parameter. -/
def FnDecl.storesOk (D : Decls) (IP : Name → Nat → Bool) (writes : Bool) (d : FnDecl) : Bool :=
  (d.markMoves.body.storesIn D (D.modeEnv.allShared d.params d.body) IP writes
    d.ownAtStart).isSome

/-- Whether the walk of `main`'s body, with its last uses marked, passes. -/
def Expr.mainStoresOk (D : Decls) (IP : Name → Nat → Bool) (writes : Bool) (main : Expr) : Bool :=
  ((main.markMoves .empty false).storesIn D (D.modeEnv.allShared [] main) IP writes []).isSome

end Stilt
