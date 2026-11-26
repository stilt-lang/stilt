import Stilt.Handling

/-!
# The fact `locks` and E0430

shared.locks: running a `when` gives a function the inferred fact `locks`, inferred as the
implicit effects are (facts.inference). A site of it is a `when`, a use of a function that
has it, called or used as a value, and a closure literal's body is part of the code that
writes it, a handler's bodies among them. A call through a function value adds nothing
(facts.calls-through-function-values): `Expr.lockFree` reads the callee as any expression,
and a function value is no site. A `with` and a performance add nothing either.

`Decls.locks` is the set of functions that have the fact: the least fixed point of
`Decls.lockSites`, from no function, each round adding the functions whose bodies hold a
site given the last. The sets grow, so they settle within one round for each function;
the model counts that many rounds and one more, and takes every function as locking if
they haven't settled, which is no less than the fixed point. Either way the set is closed:
a function outside it has a body without a site (`Decls.locks_closed`).

E0430 rejects a `when` whose block holds a site of `locks`: `Program.Locks` asks it of the
block of every `when` the program writes, those in closure literals included
(`Expr.whenBlocks`). The model leaves out `without locks` (E0204 at each site) and what
`stilt show` prints.
-/

namespace Stilt

/-- Whether a method `Trait.m` may be a function that has `locks`: the function `m` of some
impl of the trait does. A use whose type has no head yet, inside a generic body, counts each
impl it may pick. -/
def Decls.methodLocks (D : Decls) (L : List Name) (trait m : Name) : Bool :=
  D.traitImpls.any fun i => i.trait == trait && decide (implName trait i.type m ∈ L)

mutual

/-- Whether `e` holds no site of `locks`, the functions of `L` being those that have it
(shared.locks): no `when`, no use of a function of `L`, called or as a value, and no closure
literal whose body holds one. A call through a function value adds nothing
(facts.calls-through-function-values), nor does a performance or a `with`. Of that paragraph,
this states what it says of `locks`: the implicit effects and capabilities are other checks'. -/
def Expr.lockFree (D : Decls) (L : List Name) : Expr → Bool
  | .var _ | .move _ | .int _ | .bool _ | .unit | .break | .continue => true
  | .fnRef f _ _ => decide (f ∉ L)
  | .method t m _ => !D.methodLocks L t m
  | .held _ _ _ => false
  | .closure _ _ _ body => body.lockFree D L
  | .record _ fields => fieldsLockFree D L fields
  | .variant _ _ es | .list _ es | .op _ es | .view es => exprsLockFree D L es
  | .field e _ | .raise e | .try e | .return e | .loop e | .perform _ e => e.lockFree D L
  | .index a b | .seq a b | .letIn _ _ a b | .varIn _ _ a b | .for _ _ a b | .while a b
  | .tryCatch a _ _ b _ | .withH _ _ a b => a.lockFree D L && b.lockFree D L
  | .call callee args _ => callee.lockFree D L && argsLockFree D L args
  | .assign ⟨_, path⟩ value => pathLockFree D L path && value.lockFree D L
  | .if c _ a b => c.lockFree D L && a.lockFree D L && b.lockFree D L
  | .match e _ arms => e.lockFree D L && armsLockFree D L arms

def exprsLockFree (D : Decls) (L : List Name) : List Expr → Bool
  | [] => true
  | e :: es => e.lockFree D L && exprsLockFree D L es

def fieldsLockFree (D : Decls) (L : List Name) : List (Name × Expr) → Bool
  | [] => true
  | (_, e) :: fields => e.lockFree D L && fieldsLockFree D L fields

def argsLockFree (D : Decls) (L : List Name) : List Arg → Bool
  | [] => true
  | .value e :: args => e.lockFree D L && argsLockFree D L args
  | .inout ⟨_, path⟩ :: args => pathLockFree D L path && argsLockFree D L args

def pathLockFree (D : Decls) (L : List Name) : List Projection → Bool
  | [] => true
  | .field _ :: path => pathLockFree D L path
  | .index i :: path => i.lockFree D L && pathLockFree D L path

def armsLockFree (D : Decls) (L : List Name) : List Arm → Bool
  | [] => true
  | ⟨_, _, body⟩ :: arms => body.lockFree D L && armsLockFree D L arms

end

/-- The functions whose bodies hold a site of `locks`, given that those of `L` have it. -/
def Decls.lockSites (D : Decls) (L : List Name) : List Name :=
  (D.fns.filter fun d => !d.body.lockFree D L).map (·.name)

/-- `k` more rounds of `lockSites` from `L`, stopping once a round adds nothing; every
function once no round is left. -/
def Decls.locksAfter (D : Decls) : Nat → List Name → List Name
  | 0, _ => D.fns.map (·.name)
  | k + 1, L =>
    let L' := D.lockSites L
    if L'.all (· ∈ L) then L else D.locksAfter k L'

/-- The functions that have the inferred fact `locks` (shared.locks and facts.inference): the
fixed point of `lockSites` from no function. -/
def Decls.locks (D : Decls) : List Name := D.locksAfter (D.fns.length + 1) []

/-- Every function outside `L` has a body without a site of `locks`. -/
def Decls.LocksClosed (D : Decls) (L : List Name) : Prop :=
  ∀ d ∈ D.fns, d.name ∉ L → d.body.lockFree D L = true

theorem Decls.locksAfter_closed (D : Decls) : ∀ (k : Nat) (L : List Name),
    D.LocksClosed (D.locksAfter k L)
  | 0, _, d, hd, hn => absurd (List.mem_map_of_mem hd) hn
  | k + 1, L, d, hd, hn => by
    simp only [Decls.locksAfter] at hn ⊢
    split <;> rename_i hall
    · rw [ite_eq_left hall] at hn
      cases hb : d.body.lockFree D L with
      | true => rfl
      | false =>
        refine absurd (List.all_eq_true.1 hall d.name ?_) (by simpa using hn)
        exact List.mem_map_of_mem (List.mem_filter.2 ⟨hd, by simp [hb]⟩)
    · rw [ite_eq_right hall] at hn
      exact Decls.locksAfter_closed D k _ d hd hn

/-- The functions outside `Decls.locks` have bodies without a site of `locks`. -/
theorem Decls.locks_closed (D : Decls) : D.LocksClosed D.locks :=
  D.locksAfter_closed _ _

mutual

/-- The blocks of the `when`s that `e` writes, at any depth, those in closure literals
included. -/
def Expr.whenBlocks : Expr → List Expr
  | .var _ | .move _ | .int _ | .bool _ | .unit | .break | .continue | .fnRef _ _ _
  | .method _ _ _ => []
  | .held _ hs body => exprsWhenBlocks hs ++ body :: body.whenBlocks
  | .closure _ _ _ body => body.whenBlocks
  | .record _ fields => fieldsWhenBlocks fields
  | .variant _ _ es | .list _ es | .op _ es | .view es => exprsWhenBlocks es
  | .field e _ | .raise e | .try e | .return e | .loop e | .perform _ e => e.whenBlocks
  | .index a b | .seq a b | .letIn _ _ a b | .varIn _ _ a b | .for _ _ a b | .while a b
  | .tryCatch a _ _ b _ | .withH _ _ a b => a.whenBlocks ++ b.whenBlocks
  | .call callee args _ => callee.whenBlocks ++ argsWhenBlocks args
  | .assign ⟨_, path⟩ value => pathWhenBlocks path ++ value.whenBlocks
  | .if c _ a b => c.whenBlocks ++ a.whenBlocks ++ b.whenBlocks
  | .match e _ arms => e.whenBlocks ++ armsWhenBlocks arms

def exprsWhenBlocks : List Expr → List Expr
  | [] => []
  | e :: es => e.whenBlocks ++ exprsWhenBlocks es

def fieldsWhenBlocks : List (Name × Expr) → List Expr
  | [] => []
  | (_, e) :: fields => e.whenBlocks ++ fieldsWhenBlocks fields

def argsWhenBlocks : List Arg → List Expr
  | [] => []
  | .value e :: args => e.whenBlocks ++ argsWhenBlocks args
  | .inout ⟨_, path⟩ :: args => pathWhenBlocks path ++ argsWhenBlocks args

def pathWhenBlocks : List Projection → List Expr
  | [] => []
  | .field _ :: path => pathWhenBlocks path
  | .index i :: path => i.whenBlocks ++ pathWhenBlocks path

def armsWhenBlocks : List Arm → List Expr
  | [] => []
  | ⟨_, _, body⟩ :: arms => body.whenBlocks ++ armsWhenBlocks arms

end

/-- The blocks of the `when`s of every body of a program, and of `main`. -/
def Program.whenBlocks (p : Program) : List Expr :=
  p.decls.fns.flatMap (·.body.whenBlocks) ++ p.main.whenBlocks

/-- E0430 (shared.locks): no `when` of the program has a block that holds a site of `locks`,
which would be a `when` inside a `when`. -/
def Program.Locks (p : Program) : Prop :=
  ∀ b ∈ p.whenBlocks, b.lockFree p.decls p.decls.locks = true

end Stilt
