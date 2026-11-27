import Stilt.Modes.Types
import Stilt.Free

/-!
# The thread axes

Portability and contention, the two axes of modes.bindings-and-axes that read a binding's type
(modes.fixed-values, modes.contended-values and modes.mode-crossing). A binding is `fixed` when
its type holds a fixed type, `View<T>` in the calculus (views.fixed), and `contended` when its
type holds a `Shared<T>` (shared.std-sync); a closure literal is either when a binding it
captures is. The type's declaration is read once, never its values' history: no type of the
calculus has mutable heap state of its own, so a type holds what its declaration says.

A type holds itself and the parts of what it holds: a list's, a set's and an array's elements, a
map's keys and values, a tuple's elements, a record's fields and a variant's payloads at its type
arguments, and the arguments themselves, and for a function type, the values its calls give back
and those they write through its `inout` parameters (`Decls.holds`). What a closure captures
is no part of its type: a closure literal's points read its captures (`closureAxis`), which
the scope of each point of a body knows (`AxisScope`). A `match` arm's binders carry no type
in the calculus, so they take the points of the value matched, which holds what they hold, and
the greatest points when the model can't tell that value's.
-/

namespace Stilt

namespace Decls

mutual

/-- Whether `τ` holds a type that `p` accepts, where `step` answers for the fields and payloads
of record and variant types and `seen` holds those on the way to `τ`. A type reached again holds
what its first visit found, but for its type arguments, which are read at each visit. -/
def holdsStep (D : Decls) (p : Ty → Bool) (step : List Name → Ty → Bool) (seen : List Name)
    (τ : Ty) : Bool :=
  p τ || match τ with
    | .list e | .set e | .view e | .shared e => D.holdsStep p step seen e
    | .map κ σ => D.holdsStep p step seen κ || D.holdsStep p step seen σ
    | .tuple τs => D.holdsSteps p step seen τs
    | .fn ps r _ => D.holdsParams p step seen ps || D.holdsStep p step seen r
    | .record R args =>
      D.holdsSteps p step seen args || (!seen.contains R &&
        match D.record? R with
        | some r => (r.fieldsAt args).any fun (_, σ) => step (R :: seen) σ
        | none => false)
    | .variant T args =>
      D.holdsSteps p step seen args || (!seen.contains T &&
        match D.variant? T with
        | some t => (t.ctorsAt args).any fun (_, σs) => σs.any (step (T :: seen))
        | none => false)
    | _ => false

/-- Whether some type of a list holds one that `p` accepts. -/
def holdsSteps (D : Decls) (p : Ty → Bool) (step : List Name → Ty → Bool) (seen : List Name) :
    List Ty → Bool
  | [] => false
  | τ :: τs => D.holdsStep p step seen τ || D.holdsSteps p step seen τs

/-- Whether the type of some `inout` parameter of a function type holds one that `p` accepts:
what a call writes through it is a part of what the function gives. -/
def holdsParams (D : Decls) (p : Ty → Bool) (step : List Name → Ty → Bool) (seen : List Name) :
    List (Mode × Ty) → Bool
  | [] => false
  | (m, τ) :: ps => (m == .inout && D.holdsStep p step seen τ) || D.holdsParams p step seen ps

end

/-- Whether `τ` holds a type that `p` accepts, with `fuel` for the record and variant types on
the way. Each step into a declaration adds a new name, so fuel past the number of declared types
never runs out, and when it does the answer is the conservative one. -/
def holdsIn (D : Decls) (p : Ty → Bool) : Nat → List Name → Ty → Bool
  | 0, _, _ => true
  | n + 1, seen, τ => D.holdsStep p (D.holdsIn p n) seen τ

/-- Whether `τ` holds a type that `p` accepts: itself, or a part of what it holds, as the
declarations state them, which it reads once, never a value's history (modes.mode-crossing). -/
def holds (D : Decls) (p : Ty → Bool) (τ : Ty) : Bool :=
  D.holdsIn p (D.records.length + D.variants.length + 1) [] τ

/-- Whether `τ` holds a `Shared<T>` (modes.contended-values). -/
def contended (D : Decls) (τ : Ty) : Bool :=
  D.holds (fun | .shared _ => true | _ => false) τ

/-- Whether `τ` holds a fixed type, `View<T>` (modes.fixed-values and views.fixed). -/
def fixedTy (D : Decls) (τ : Ty) : Bool :=
  D.holds (fun | .view _ => true | _ => false) τ

end Decls

/-- A binding's point on one thread axis, `fixed` or `contended` when `has` says so of its
type, and the greatest point when the model doesn't know its type. -/
def axisOf (has : Ty → Bool) : Option Ty → Bool
  | some τ => has τ
  | none => true

/-- These modes with the points on the thread axes: `fixed` when `fixed`, and `contended` when
`contended`. -/
def Modes.threads (m : Modes) (fixed contended : Bool) : Modes :=
  { m with portability := if fixed then .fixed else .portable,
           contention := if contended then .contended else .calm }

/-- What one thread axis knows of the bindings in scope, the newest first: whether each is at
the axis's greatest point. -/
abbrev AxisScope := List (Name × Bool)

/-- The point of a closure literal with parameters `ps`, result `r` and row `ρ`, in the scope
`scope`: its type's, or the greatest when a binding it captures is there, as a closure literal
that captures a `fixed` binding is `fixed` (modes.fixed-values), and one that captures a
`contended` binding `contended`. -/
def closureAxis (has : Ty → Bool) (scope : AxisScope) (ps : List Param) (r : Ty) (ρ : Row)
    (body : Expr) : Bool :=
  has (.fn (ps.map Param.sig) r ρ) || (captureOf ps body scope).any (·.2)

/-- The point of a binding of type `τ` whose initializer is `init`: a closure literal's when
it is one, its type's otherwise. -/
def bindingAxis (has : Ty → Bool) (scope : AxisScope) (τ : Ty) : Expr → Bool
  | .closure ps r ρ body => closureAxis has scope ps r ρ body
  | _ => has τ

/-- The point of an expression's value where the model can tell it: a variable's, a call's by
its result type, a literal's by its type, a closure literal's by its captures, and a part of a
value at most its whole's. -/
def Expr.axisOf? (has : Ty → Bool) (scope : AxisScope) : Expr → Option Bool
  | .var y | .move y => scope.lookup y
  | .call _ _ τ => some (has τ)
  | .list τ _ => some (has (.list τ))
  | .record R args _ => some (has (.record R args))
  | .variant T args _ _ => some (has (.variant T args))
  | .closure ps r ρ body => some (closureAxis has scope ps r ρ body)
  | .field e _ | .index e _ => e.axisOf? has scope
  | _ => none

/-- The scope of the part at position `n` of an expression in the scope `scope`, in the order
of `Stilt.Modes.Traverse`: a binding's body sees the binding, a closure literal's body its
parameters, a `when`'s block its names, and an arm its binders, which hold what the matched
value holds. -/
def axisChild (has : Ty → Bool) (scope : AxisScope) : Expr → Nat → AxisScope
  | .letIn y τ init _, 1 | .varIn y τ init _, 1 => (y, bindingAxis has scope τ init) :: scope
  | .for y τ _ _, 1 | .tryCatch _ τ y _ _, 1 => (y, has τ) :: scope
  | .closure ps _ _ _, _ => ps.map (fun p => (p.name, has p.type)) ++ scope
  | .held ns hs _, n =>
    if n == hs.length then ns.map (fun (y, τ) => (y, has τ)) ++ scope else scope
  | .match s _ arms, n + 1 =>
    let t := (s.axisOf? has scope).getD (axisOf has none)
    ((arms[n]?.map (·.binders)).getD []).map (·, t) ++ scope
  | _, _ => scope

/-- `Shared<T>` is contended (modes.contended-values). -/
theorem Decls.contended_shared (D : Decls) (u : Ty) : D.contended (.shared u) = true := by
  simp [Decls.contended, Decls.holds, Decls.holdsIn, Decls.holdsStep]

/-- `View<T>` is fixed (views.fixed). -/
theorem Decls.fixedTy_view (D : Decls) (u : Ty) : D.fixedTy (.view u) = true := by
  simp [Decls.fixedTy, Decls.holds, Decls.holdsIn, Decls.holdsStep]

end Stilt
