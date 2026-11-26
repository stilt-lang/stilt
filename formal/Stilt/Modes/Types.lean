import Stilt.Modes.Lattice
import Stilt.Places
import Stilt.Generics

/-!
# Copy-on-write types

The types whose values hold memory that a write may copy: the types on which
locality and uniqueness are facts (modes.escaping and modes.copy-on-write-types). The calculus has no
`Map`, so a copy-on-write type of the model is `str`, `List<T>`, a function
type, a recursive type (facts.allocation), or a record, tuple or variant type
with a field, element or payload of one.

A part of a binding is reached by fields, tuple fields among them, and list
elements (`Sel`); modes.escaping and modes.copies count a part when its type is copy-on-write. Its shape is the place it
is, with every index removed (modes.overlap), which is what a copy and a
write compare.
-/

namespace Stilt

/-- A step from a value to a part of it: a field, or an element of a list; or a step to a
part the analysis no longer knows, which may be any part (modes.shared-writes). -/
inductive Sel where
  | field (name : Name)
  | elem
  | any
  deriving DecidableEq, Repr

/-- The step of a projection, an index kept only as a position. -/
def Projection.sel : Projection → Sel
  | .field f => .field f
  | .index _ => .elem

/-- The shape of a part: its fields up to the first element, since `a[i]`
counts as all of `a` (modes.overlap), and up to a step to any part, which counts as all of what
it steps from. -/
def Sel.shape : List Sel → List Name
  | .field f :: sels => f :: Sel.shape sels
  | _ => []

namespace Decls

mutual

/-- Whether `τ` is a copy-on-write type (modes.copy-on-write-types), where `step`
answers for the types of the fields and payloads of record and variant types,
with `seen` holding the record and variant types on the way to `τ`. A tuple is
one when an element is, and a type parameter is one, since it may stand for
one. A set is one, as a record with a field of a map type. -/
def cowStep (D : Decls) (step : List Name → Ty → Bool) (seen : List Name) : Ty → Bool
  | .int _ | .float _ | .bool | .unit | .never => false
  | .str | .list _ | .map _ _ | .set _ | .fn _ _ _ | .param _ => true
  | .view _ | .shared _ => false
  | .tuple τs => cowSteps D step seen τs
  | .record R args =>
    seen.contains R ||
      match D.record? R with
      | some r => (r.fieldsAt args).any fun (_, τ) => step (R :: seen) τ
      | none => false
  | .variant T args =>
    seen.contains T ||
      match D.variant? T with
      | some t => (t.ctorsAt args).any fun (_, τs) => τs.any (step (T :: seen))
      | none => false

/-- Whether some type of a list is a copy-on-write type. -/
def cowSteps (D : Decls) (step : List Name → Ty → Bool) (seen : List Name) : List Ty → Bool
  | [] => false
  | τ :: τs => D.cowStep step seen τ || cowSteps D step seen τs

end

/-- Whether `τ` is a copy-on-write type (modes.copy-on-write-types), with `fuel` to spend
on record and variant types and `seen` holding those on the way to `τ`. A type
that reaches one of them again is recursive (declarations.recursive-types). Fuel runs out
only past every declared type, and then the answer is the conservative one. -/
def cowIn (D : Decls) : Nat → List Name → Ty → Bool
  | 0, _, _ => true
  | n + 1, seen, τ => D.cowStep (D.cowIn n) seen τ

/-- Whether `τ` is a copy-on-write type: `str`, `List<T>`, `Map<K, V>`, a
function type, a recursive type, or a record, tuple or variant type with a
field, element or payload of one (modes.copy-on-write-types). -/
def cow (D : Decls) (τ : Ty) : Bool := D.cowIn (D.records.length + D.variants.length + 1) [] τ

/-- The type of the part of a value of type `τ` that `sels` reaches. -/
def partType (D : Decls) : Ty → List Sel → Option Ty
  | τ, [] => some τ
  | .record R args, .field f :: sels =>
    match (D.record? R).bind ((·.fieldsAt args |>.lookup f)) with
    | some τ => D.partType τ sels
    | none => none
  | .tuple τs, .field f :: sels =>
    match (positions τs).lookup f with
    | some τ => D.partType τ sels
    | none => none
  | .list τ, .elem :: sels => D.partType τ sels
  | _, _ => none

/-- Whether the part `sels` of a binding of type `τ` counts for locality and
copies: its type is copy-on-write (modes.escaping and modes.copies). A part whose type
the model can't find counts. -/
def cowPart (D : Decls) (τ : Ty) (sels : List Sel) : Bool :=
  match D.partType τ sels with
  | some σ => D.cow σ
  | none => true

end Decls

/-- Strings, lists and functions are copy-on-write, and numbers aren't
(modes.copy-on-write-types). -/
theorem Decls.cow_str (D : Decls) : D.cow .str = true := rfl

theorem Decls.cow_list (D : Decls) (τ : Ty) : D.cow (.list τ) = true := rfl

theorem Decls.cow_fn (D : Decls) (ps : List (Mode × Ty)) (r : Ty) (ρ : Row) :
    D.cow (.fn ps r ρ) = true := rfl

theorem Decls.cow_i64 (D : Decls) : D.cow .i64 = false := rfl

/-- A whole binding is the part reached by nothing. -/
theorem Decls.cowPart_nil (D : Decls) (τ : Ty) : D.cowPart τ [] = D.cow τ := rfl

end Stilt
