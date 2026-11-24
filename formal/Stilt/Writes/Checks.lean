import Stilt.Writes.Syntax

/-!
# The checks of writable views

The sources of a view and what it writes (projections.what-view-writes), the law of
exclusivity with the reads of views (E0423) and their writes (E0429), the
views that a `var` binding is given (projections.writable-bindings, E0428), and the check that no
view outlives its source (views.escaping, E0422).

A shape is a root here, so a source is a name, and two places overlap when
they have the same root (modes.overlap).
-/

namespace Stilt.Writes

open Stilt.Views (VTy)

/-- The bindings in scope, the newest first, each with the sources of the view
it holds, and none for one that holds a value. -/
abbrev Sources := List (Name × List Name)

/-- Drops the names of the outer bindings of `x`, which a new binding of `x`
hides, as `Stilt.hide` does for shapes. -/
def hide (names : List Name) (x : Name) : List Name := names.filter (· != x)

/-- What a binding of `x` holds as the sources of its view, given its
initializer's `S`. A view made from a writable binding has the binding as its
source (projections.places-through-views); the model adds what the binding writes, which its
scope keeps from every access already (projections.what-view-writes). -/
def held (w : Bool) (x : Name) (S : List Name) : List Name := if w then x :: S else S

/-- The reads in the scope of a binding: a binding that doesn't write reads
its initializer's sources (views.reads-that-last; projections.what-view-writes). -/
def readsIn (w : Bool) (S R : List Name) : List Name := if w then R else S ++ R

/-- The writes in the scope of a binding: a writable binding holds what its
view writes as a modification (projections.what-view-writes). -/
def writesIn (w : Bool) (S W : List Name) : List Name := if w then S ++ W else W

/-- The sources of the view an expression gives (views.making-view): the root of
the place `View.of` or `view.into` was given, those of the view a part is
taken from, those of a binding. A block's view has its last expression's. -/
def WExpr.sources (Γ : Sources) : WExpr → List Name
  | .var x => (Γ.lookup x).getD []
  | .viewOf src _ _ | .into src _ _ => src.root?.toList
  | .sub v _ _ => v.sources Γ
  | .letIn x _ init body => body.sources ((x, init.sources Γ) :: Γ)
  | .varIn x τ init body => body.sources ((x, held (writable τ) x (init.sources Γ)) :: Γ)
  | .seq _ b => b.sources Γ
  | _ => []

/-- Whether the view an expression gives writes every source it has: one that
`view.into` made, as a block's last expression or not (projections.writable-views, projections.what-view-writes and projections.writable-bindings).
A view read from a binding reads it, and `View.of` and `v.view` read. -/
def WExpr.writes : WExpr → Bool
  | .into _ _ _ => true
  | .letIn _ _ _ body | .varIn _ _ _ body | .seq _ body => body.writes
  | _ => false

/-- Whether `x` may be read: no writable binding writes it (projections.what-view-writes,
E0429), when `locks` checks it. -/
def readable (locks : Bool) (W : List Name) (x : Name) : Bool := !locks || !W.contains x

/-- Whether `x` may be modified: no view reads it (views.change-while-viewed, E0423), and
none writes it (projections.what-view-writes, E0429). -/
def modifiable (locks : Bool) (R W : List Name) (x : Name) : Bool :=
  !R.contains x && readable locks W x

mutual

/-- Whether `e` obeys the law of exclusivity (modes.law) while views read
`R` and writable bindings write `W`, with the sources `Γ`. A view that no
binding holds, and any binding but a writable one, reads its sources for the
durations of views.reads-that-last, whatever it writes; a writable binding writes
what its view writes for its scope (projections.what-view-writes). A modification of what a
view reads is E0423; any access to what a writable binding writes, a read
among them, is E0429, when `locks` holds. A place's indexes are accesses. -/
def WExpr.exclusive (locks : Bool) (Γ : Sources) (R W : List Name) : WExpr → Bool
  | .var x => readable locks W x
  | .int _ => true
  | .list _ es => exprsExclusive locks Γ R W es
  | .index e i => e.exclusive locks Γ R W && i.exclusive locks Γ (e.sources Γ ++ R) W
  | .letIn x _ init body =>
    init.exclusive locks Γ R W &&
      body.exclusive locks ((x, init.sources Γ) :: Γ) (hide (init.sources Γ ++ R) x) (hide W x)
  | .varIn x τ init body =>
    init.exclusive locks Γ R W &&
      body.exclusive locks ((x, held (writable τ) x (init.sources Γ)) :: Γ)
        (hide (readsIn (writable τ) (init.sources Γ) R) x)
        (hide (writesIn (writable τ) (init.sources Γ) W) x)
  | .assign t v =>
    t.placeExclusive locks Γ R W && v.exclusive locks Γ R W && t.root?.all (modifiable locks R W)
  | .seq a b => a.exclusive locks Γ R W && b.exclusive locks Γ R W
  | .viewOf src a b =>
    src.placeExclusive locks Γ R W && src.root?.all (readable locks W) &&
      a.exclusive locks Γ R W && b.exclusive locks Γ R W
  | .into src a b =>
    src.placeExclusive locks Γ R W && src.root?.all (modifiable locks R W) &&
      a.exclusive locks Γ R W && b.exclusive locks Γ R W
  | .sub v a b =>
    v.exclusive locks Γ R W && a.exclusive locks Γ (v.sources Γ ++ R) W &&
      b.exclusive locks Γ (v.sources Γ ++ R) W
  | .len v => v.exclusive locks Γ R W

/-- Whether the indexes of a place obey the law. -/
def WExpr.placeExclusive (locks : Bool) (Γ : Sources) (R W : List Name) : WExpr → Bool
  | .index e i => e.placeExclusive locks Γ R W && i.exclusive locks Γ R W
  | _ => true

/-- Whether every expression of a list obeys the law. -/
def exprsExclusive (locks : Bool) (Γ : Sources) (R W : List Name) : List WExpr → Bool
  | [] => true
  | e :: es => e.exclusive locks Γ R W && exprsExclusive locks Γ R W es

end

mutual

/-- Whether every writable binding is given a view that writes every source it
has (projections.writable-bindings, E0428). -/
def WExpr.bound : WExpr → Bool
  | .var _ | .int _ => true
  | .list _ es => exprsBound es
  | .index a b | .assign a b | .seq a b => a.bound && b.bound
  | .letIn _ _ init body => init.bound && body.bound
  | .varIn _ τ init body => (!writable τ || init.writes) && init.bound && body.bound
  | .viewOf c a b | .into c a b | .sub c a b => c.bound && a.bound && b.bound
  | .len e => e.bound

/-- Whether every expression of a list passes E0428. -/
def exprsBound : List WExpr → Bool
  | [] => true
  | e :: es => e.bound && exprsBound es

end

mutual

/-- Whether no view outlives its source (views.escaping, E0422): the rest of a
block reads no binding that the block makes. -/
def WExpr.contained (Γ : Sources) : WExpr → Bool
  | .var _ | .int _ => true
  | .list _ es => exprsContained Γ es
  | .len e => e.contained Γ
  | .index a b | .assign a b | .seq a b => a.contained Γ && b.contained Γ
  | .letIn x _ init body =>
    init.contained Γ && body.contained ((x, init.sources Γ) :: Γ) &&
      (body.sources ((x, init.sources Γ) :: Γ)).all (· != x)
  | .varIn x τ init body =>
    init.contained Γ && body.contained ((x, held (writable τ) x (init.sources Γ)) :: Γ) &&
      (body.sources ((x, held (writable τ) x (init.sources Γ)) :: Γ)).all (· != x)
  | .viewOf c a b | .into c a b | .sub c a b => c.contained Γ && a.contained Γ && b.contained Γ

/-- Whether no view of a list outlives its source. -/
def exprsContained (Γ : Sources) : List WExpr → Bool
  | [] => true
  | e :: es => e.contained Γ && exprsContained Γ es

end

namespace WProgram

/-- The body obeys the law of exclusivity with the reads and writes of views:
E0423 and E0429 reject nothing in it (projections.what-view-writes). -/
def Exclusive (p : WProgram) : Prop := p.body.exclusive true [] [] [] = true

/-- Every writable binding of the body writes what its view has as sources:
E0428 rejects nothing in it (projections.writable-bindings). -/
def Bound (p : WProgram) : Prop := p.body.bound = true

/-- No view of the body outlives its source: E0422 rejects nothing in it
(views.escaping). -/
def Contained (p : WProgram) : Prop := p.body.contained [] = true

end WProgram

end Stilt.Writes
