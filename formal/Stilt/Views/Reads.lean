import Stilt.Exclusivity
import Stilt.Views.Syntax

/-!
# The reads of views

The sources of a view (views.making-view), the reads that views make and how long
they last (views.reads-that-last), and the law of exclusivity of modes.law extended with them,
under which a modification that overlaps a source while a view of it lives is
E0423 (views.change-while-viewed). views.escaping, that a view can't outlive its source, is the check
`VExpr.contained` (E0422).

The analysis is lexical and syntactic, as the reference interpreter's is: a source is a
place's shape, which `Shape.overlaps` compares as modes.overlap does. A
temporary has no shape: nothing can name it, so nothing can change it.
-/

namespace Stilt.Views

/-- The sources of the bindings in scope, the newest first: for each, the
places that the view it holds reads, and none for a binding that holds no
view. -/
abbrev Sources := List (Name × List Shape)

/-- The places a value reads, if it is a view (views.making-view): a view made
from a place reads the place, a part of a view reads what the view reads, a
view bound to a variable reads what its initializer read, and a view made from
any other expression reads a temporary, which has no shape. A block's value
reads what its last expression's does, and an `if`'s what either branch's
does. -/
def VExpr.sources (Γ : Sources) : VExpr → List Shape
  | .var x => (Γ.lookup x).getD []
  | .viewOf src _ _ => src.shape?.toList
  | .sub v _ _ => v.sources Γ
  | .letIn x _ init body => body.sources ((x, init.sources Γ) :: Γ)
  | .varIn x _ init body => body.sources ((x, init.sources Γ) :: Γ)
  | .seq _ b => b.sources Γ
  | .if _ _ a b => a.sources Γ ++ b.sources Γ
  | _ => []

/-- The place a `for` loop over a list reads for its body, if its iterable is
a place (modes.durations). A modification of it is E0404. -/
def iterated (e : VExpr) : List Shape := e.shape?.toList

mutual

/-- Whether `e` obeys the law of exclusivity (modes.law) while the places
`reading` are read, with the sources `Γ` of the views in scope. When `loops`
holds, a `for` loop over a list reads its iterable for its body, which E0404
protects; without it, only the reads of views count.

views.reads-that-last gives views these durations: a binding of a view is a read of
its sources for the binding's scope, as `for p in e` reads `e` for its body,
and so is the view that a `for` over a view iterates (views.for-over-view). A view that no
binding holds reads its sources from where it is made, for as long as the
expression that holds it still runs: here, while the index of `v[i]` and the
offsets of `v.view(a, b)` are evaluated. views.reads-that-last lets that read last to the end
of the statement, so this pass accepts every program that views.reads-that-last accepts. A
modification of a place that overlaps any of these reads is E0423 (views.change-while-viewed). -/
def VExpr.exclusive (loops : Bool) (Γ : Sources) (reading : List Shape) : VExpr → Bool
  | .var _ | .int _ | .bool _ | .unit => true
  | .record _ fields => fieldsExclusive loops Γ reading fields
  | .list _ es => exprsExclusive loops Γ reading es
  | .field e _ | .len e | .copy e => e.exclusive loops Γ reading
  | .index e i => e.exclusive loops Γ reading && i.exclusive loops Γ (e.sources Γ ++ reading)
  | .letIn x _ init body | .varIn x _ init body =>
    init.exclusive loops Γ reading &&
      body.exclusive loops ((x, init.sources Γ) :: Γ) (hide (init.sources Γ ++ reading) x)
  | .assign target value =>
    target.placeExclusive loops Γ reading && value.exclusive loops Γ reading &&
      target.shape?.all (unread reading)
  | .seq a b => a.exclusive loops Γ reading && b.exclusive loops Γ reading
  | .if c _ a b =>
    c.exclusive loops Γ reading && a.exclusive loops Γ reading && b.exclusive loops Γ reading
  | .for x _ it body =>
    it.exclusive loops Γ reading &&
      body.exclusive loops ((x, []) :: Γ)
        (hide (it.sources Γ ++ ((if loops then iterated it else []) ++ reading)) x)
  | .viewOf src start stop =>
    (match src.shape? with
      | some _ => src.placeExclusive loops Γ reading
      | none => src.exclusive loops Γ reading) &&
      start.exclusive loops Γ reading && stop.exclusive loops Γ reading
  | .sub v start stop =>
    v.exclusive loops Γ reading && start.exclusive loops Γ (v.sources Γ ++ reading) &&
      stop.exclusive loops Γ (v.sources Γ ++ reading)

/-- Whether the indexes of a place obey the law. A place is evaluated as the
target of an assignment or the source of a view, which reads its value only
afterwards. -/
def VExpr.placeExclusive (loops : Bool) (Γ : Sources) (reading : List Shape) : VExpr → Bool
  | .field e _ => e.placeExclusive loops Γ reading
  | .index e i => e.placeExclusive loops Γ reading && i.exclusive loops Γ reading
  | _ => true

/-- Whether every expression of a list obeys the law. -/
def exprsExclusive (loops : Bool) (Γ : Sources) (reading : List Shape) : List VExpr → Bool
  | [] => true
  | e :: es => e.exclusive loops Γ reading && exprsExclusive loops Γ reading es

/-- Whether every field of a record literal obeys the law. -/
def fieldsExclusive (loops : Bool) (Γ : Sources) (reading : List Shape) :
    List (Name × VExpr) → Bool
  | [] => true
  | (_, e) :: fields => e.exclusive loops Γ reading && fieldsExclusive loops Γ reading fields

end

mutual

/-- Whether no view outlives its source (views.escaping, E0422): the rest of a
block, whose value the block gives, reads no binding that the block makes,
whose storage ends with it. A function's body is a block, so its result views
none of its locals, only its `let` parameters. -/
def VExpr.contained (Γ : Sources) : VExpr → Bool
  | .var _ | .int _ | .bool _ | .unit => true
  | .record _ fields => fieldsContained Γ fields
  | .list _ es => exprsContained Γ es
  | .field e _ | .len e | .copy e => e.contained Γ
  | .index a b | .assign a b | .seq a b => a.contained Γ && b.contained Γ
  | .letIn x _ init body | .varIn x _ init body =>
    init.contained Γ && body.contained ((x, init.sources Γ) :: Γ) &&
      (body.sources ((x, init.sources Γ) :: Γ)).all (·.root != x)
  | .if c _ a b | .viewOf c a b | .sub c a b => c.contained Γ && a.contained Γ && b.contained Γ
  | .for x _ it body => it.contained Γ && body.contained ((x, []) :: Γ)

/-- Whether no view of a list outlives its source. -/
def exprsContained (Γ : Sources) : List VExpr → Bool
  | [] => true
  | e :: es => e.contained Γ && exprsContained Γ es

/-- Whether no view of a record literal outlives its source. -/
def fieldsContained (Γ : Sources) : List (Name × VExpr) → Bool
  | [] => true
  | (_, e) :: fields => e.contained Γ && fieldsContained Γ fields

end

namespace VProgram

/-- The sources of the parameters, which hold no view. -/
def sources (p : VProgram) : Sources := p.args.map fun a => (a.1, [])

/-- The body obeys the law of exclusivity of modes.law with the reads of views:
E0404 and E0423 reject nothing in it (views.change-while-viewed). -/
def Exclusive (p : VProgram) : Prop := p.body.exclusive true p.sources [] = true

/-- The body obeys the law with the reads of views alone: E0423 rejects
nothing in it, whatever E0404 says. -/
def ViewsExclusive (p : VProgram) : Prop := p.body.exclusive false p.sources [] = true

/-- No view of the body outlives its source: E0422 rejects nothing in it
(views.escaping). -/
def Contained (p : VProgram) : Prop := p.body.contained p.sources = true

end VProgram

end Stilt.Views
