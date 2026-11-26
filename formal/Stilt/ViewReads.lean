import Stilt.Exclusivity
import Stilt.Sources

/-!
# The reads of views

The law of exclusivity (modes.law) with the reads that views make
(views.reads-that-last): while a view of a source lives, a modification of a
place that overlaps the source is E0423 (views.change-while-viewed). The reads
of `for` loops over places and the `inout` arguments of a call are the core
law's, `Expr.exclusive` (E0404 and E0402); this pass adds those of views alone.

views.reads-that-last gives views these durations. A binding that holds a view
reads its sources for its scope, as `for p in e` reads `e` for its body, and so
does the view a `for` iterates (views.for-over-view). A view that no binding
holds reads its sources while the expression that holds it still runs: here,
while the operands after it are evaluated, up to the operation or the call
that takes it, for the whole of that call (views.across-calls). That read may
last to the end of the statement, so this pass accepts every program that
views.reads-that-last accepts. A view's read of a place starts when the place,
its source operand, is evaluated, so the offsets of `View.of` after it are
evaluated under it. A binding reads the sources it was bound with for its whole
scope, so a view assigned to it later may read only those: one that reads
another source would leave that source unread.
-/

namespace Stilt

/-- The sources of the views a call's value arguments pass, which the call
reads while it runs (views.reads-that-last). -/
def argViews (D : Decls) (Γ : ViewScope) : List Arg → List Shape
  | [] => []
  | .value e :: args => e.sources D Γ ++ argViews D Γ args
  | .inout _ :: args => argViews D Γ args

mutual

/-- Whether `e` modifies no source of a view that lives while it runs, with
the places `reading` read around it (views.change-while-viewed, E0423). -/
def Expr.viewsRead (D : Decls) (Γ : ViewScope) (reading : List Shape) : Expr → Bool
  | .var _ | .move _ | .int _ | .bool _ | .unit | .break | .continue | .fnRef _ _ _
  | .method _ _ _ => true
  | .record _ _ fields => fieldsViewsRead D Γ reading fields
  | .variant _ _ _ es | .list _ es | .op _ es => exprsViewsRead D Γ reading es
  | .view [] => true
  | .view (e :: es) =>
    e.viewsRead D Γ reading && exprsViewsRead D Γ (headSources D Γ [e] ++ reading) es
  | .field e _ | .raise e | .try e | .return e | .perform _ e | .loop e =>
    e.viewsRead D Γ reading
  | .index e i => e.viewsRead D Γ reading && i.viewsRead D Γ (e.sources D Γ ++ reading)
  | .closure ps _ _ body => body.viewsRead D (Γ.enter D ps) []
  | .call callee args _ =>
    callee.viewsRead D Γ reading && argsViewsRead D Γ (callee.sources D Γ ++ reading) args &&
      (inoutShapes args).all (unread (argViews D Γ args ++ callee.sources D Γ ++ reading))
  | .held ns hs body =>
    exprsViewsRead D Γ reading hs &&
      body.viewsRead D (Γ.holding D ns) ((ns.map Prod.fst).foldl hide reading)
  | .letIn x τ init body | .varIn x τ init body =>
    init.viewsRead D Γ reading &&
      let Γ' := Γ.bind D x τ (init.sources D Γ)
      body.viewsRead D Γ' (hide ((Γ'.lookup x).elim [] (·.sources) ++ reading) x)
  | .assign ⟨root, path⟩ value =>
    pathViewsRead D Γ reading path && value.viewsRead D Γ reading &&
      unread reading (Place.mk root path).shape &&
        (value.sources D Γ).all fun s => (Γ.lookup root).any (·.sources.contains s)
  | .seq a b | .while a b | .withH _ _ a b => a.viewsRead D Γ reading && b.viewsRead D Γ reading
  | .if c _ a b => c.viewsRead D Γ reading && a.viewsRead D Γ reading && b.viewsRead D Γ reading
  | .match e _ arms => e.viewsRead D Γ reading && armsViewsRead D Γ reading (e.sources D Γ) arms
  | .for x τ e body =>
    e.viewsRead D Γ reading &&
      body.viewsRead D (Γ.bind D x τ []) (hide (e.sources D Γ ++ reading) x)
  | .tryCatch e E x handler _ =>
    e.viewsRead D Γ reading && handler.viewsRead D (Γ.bind D x E []) (hide reading x)

/-- Whether the operands of a list, evaluated in order, modify no source that
the views among those before them read. -/
def exprsViewsRead (D : Decls) (Γ : ViewScope) (reading : List Shape) : List Expr → Bool
  | [] => true
  | e :: es => e.viewsRead D Γ reading && exprsViewsRead D Γ (e.sources D Γ ++ reading) es

/-- Whether the fields of a record literal, evaluated in order, modify no source that
the views among those before them read. -/
def fieldsViewsRead (D : Decls) (Γ : ViewScope) (reading : List Shape) :
    List (Name × Expr) → Bool
  | [] => true
  | (_, e) :: fields =>
    e.viewsRead D Γ reading && fieldsViewsRead D Γ (e.sources D Γ ++ reading) fields

/-- Whether the arguments of a call, evaluated in order, modify no source of
the views among those before them. -/
def argsViewsRead (D : Decls) (Γ : ViewScope) (reading : List Shape) : List Arg → Bool
  | [] => true
  | .value e :: args => e.viewsRead D Γ reading && argsViewsRead D Γ (e.sources D Γ ++ reading) args
  | .inout ⟨_, path⟩ :: args => pathViewsRead D Γ reading path && argsViewsRead D Γ reading args

/-- Whether the indexes of a place modify no source of a live view. -/
def pathViewsRead (D : Decls) (Γ : ViewScope) (reading : List Shape) : List Projection → Bool
  | [] => true
  | .field _ :: path => pathViewsRead D Γ reading path
  | .index i :: path => i.viewsRead D Γ reading && pathViewsRead D Γ reading path

/-- Whether the arms of a `match` modify no source of a live view. Each binder
holds what the scrutinee reads, and hides the variable of its name. -/
def armsViewsRead (D : Decls) (Γ : ViewScope) (reading scrutinee : List Shape) : List Arm → Bool
  | [] => true
  | ⟨_, binders, body⟩ :: arms =>
    body.viewsRead D (Γ.binders binders scrutinee) (binders.foldl hide reading) &&
      armsViewsRead D Γ reading scrutinee arms

end

/-- Every body of the program modifies no source of a view while the view
lives: E0423 rejects nothing in it (views.change-while-viewed). -/
def Program.ViewsRead (p : Program) : Prop :=
  (∀ d ∈ p.decls.fns, d.body.viewsRead p.decls (d.viewScope p.decls) [] = true) ∧
    p.main.viewsRead p.decls [] [] = true

end Stilt
