import Stilt.Show

/-!
# Arrays

An array type of `std.array`, `Array<T, n>`, is in the calculus a record named by the type's
own text (`arrayName`), with one field, `[]`, the list of its elements, as the export writes
it: an array is a value, copied with its elements, and its record is never the list it holds,
nor any other record. What the calculus states of arrays beside a record's rules is
`Decls.Arrays` and `Program.ArrayLiterals`, which `Program.Accepted` checks.
-/

namespace Stilt

/-- The field of an array's record that holds its elements, a name that no field a program
writes has. -/
def arrayField : Name := "[]"

/-- The size `n` that the name of an array's record writes, `std.array.Array<T, n>`: the
integer after its last `, `. -/
def arraySize? (R : Name) : Option Int :=
  (R.splitOn ", ").getLast?.bind fun s => (s.replace ">" "").toInt?

/-- The records of array types (generics.arrays): `Array<T, n>`, a sequence of `n` values of
type `T`, is the record `std.array.Array<T, n>` of one field, `[]`, of type `List<T>`, at no
type arguments, whose name writes its size, an integer.

* An element is read and written through the field: `a[i]` is `a.[][i]`, a place of the
  field's list at the index `i`, so `a[i] = v`, `a[i] += 1` and `inout a[i]` write it, and each
  panics with `bounds` unless `0 ≤ i < n`, as a list's index does. An array is a value, copied
  with its elements, which a write through a `var` or an `inout` parameter changes in that copy
  alone. No `impl` block is of it and no trait impl is for it, so it has the members of
  `std.array` alone, `len`, `n`, and `to_list`, the field's list, and its structural impls
  (generics.array-elements). `array.fill(x)` is the literal of `n` copies of `x`, after a panic
  with `bounds` when `n` is negative; `from_list` and `map` are left out.
* A `for` over an array is one over the field's list, its elements of type `T` in order
  (generics.array-iteration).
* Its structural `Eq` and `Ord` are a record's, which compare its one field, the list of its
  elements, as lists are compared and ordered, and `Show` writes it as that list is written
  (`Value.shown`, generics.array-traits); the calculus has no `Hash`. -/
structure Decls.Arrays (D : Decls) : Prop where
  records : ∀ r ∈ D.records, arrayName r.name = true →
    r.typeParams = [] ∧ (arraySize? r.name).isSome ∧ ∃ τ, r.fields = [(arrayField, .list τ)]
  noInherent : ∀ i ∈ D.impls, arrayName i.type = false
  noImpls : ∀ i ∈ D.traitImpls, ∀ R, i.type = .record R → arrayName R = false

mutual

/-- The record literals that `e` writes, at any depth, each with its record and its fields. -/
def Expr.recordLits : Expr → List (Name × List (Name × Expr))
  | .var _ | .move _ | .int _ | .bool _ | .unit | .break | .continue | .fnRef _ _ _
  | .method _ _ _ => []
  | .form _ m => m.recordLits
  | .closure _ _ _ body => body.recordLits
  | .record R _ fields => (R, fields) :: fieldsRecordLits fields
  | .variant _ _ _ es | .list _ es | .op _ es | .view es => exprsRecordLits es
  | .field e _ | .raise e | .try e | .return e | .loop e | .perform _ e => e.recordLits
  | .index a b | .seq a b | .letIn _ _ a b | .varIn _ _ a b | .for _ _ a b | .while a b
  | .tryCatch a _ _ b _ | .withH _ _ a b => a.recordLits ++ b.recordLits
  | .held _ hs body => exprsRecordLits hs ++ body.recordLits
  | .call callee args _ => callee.recordLits ++ argsRecordLits args
  | .assign ⟨_, path⟩ value => pathRecordLits path ++ value.recordLits
  | .if c _ a b => c.recordLits ++ a.recordLits ++ b.recordLits
  | .match e _ arms => e.recordLits ++ armsRecordLits arms

def exprsRecordLits : List Expr → List (Name × List (Name × Expr))
  | [] => []
  | e :: es => e.recordLits ++ exprsRecordLits es

def fieldsRecordLits : List (Name × Expr) → List (Name × List (Name × Expr))
  | [] => []
  | (_, e) :: fields => e.recordLits ++ fieldsRecordLits fields

def argsRecordLits : List Arg → List (Name × List (Name × Expr))
  | [] => []
  | .value e :: args => e.recordLits ++ argsRecordLits args
  | .inout ⟨_, path⟩ :: args => pathRecordLits path ++ argsRecordLits args

def pathRecordLits : List Projection → List (Name × List (Name × Expr))
  | [] => []
  | .field _ :: path => pathRecordLits path
  | .index i :: path => i.recordLits ++ pathRecordLits path

def armsRecordLits : List Arm → List (Name × List (Name × Expr))
  | [] => []
  | ⟨_, _, guard, body⟩ :: arms => guardRecordLits guard ++ body.recordLits ++ armsRecordLits arms

def guardRecordLits : Option Expr → List (Name × List (Name × Expr))
  | none => []
  | some g => g.recordLits

end

/-- The record literals of every body of a program, and of `main`. -/
def Program.recordLits (p : Program) : List (Name × List (Name × Expr)) :=
  p.decls.fns.flatMap (·.body.recordLits) ++ p.main.recordLits

/-- A list literal whose expected type is `Array<T, n>` makes an array: elaborated, it is the
record literal of the array's record whose field is the literal, and the literal's elements,
each of type `T`, are exactly `n`, or it is E0311 (generics.array-literals). Where no `Array`
type is expected, a list literal is a `List`, which no array's record is. -/
def Program.ArrayLiterals (p : Program) : Prop :=
  ∀ l ∈ p.recordLits, arrayName l.1 = true → ∀ τ es, l.2 = [(arrayField, Expr.list τ es)] →
    arraySize? l.1 = some (es.length : Int)

end Stilt
