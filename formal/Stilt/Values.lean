import Stilt.Declarations

/-!
# Values

Run-time values, and the paths that reach a part of a value.

Values are immutable data, as in the reference interpreter, so a copy of a value is the value
itself (values.value-semantics and values.independent-copies). A path is a place whose indexes have been
evaluated; reading and writing through one is how both models of memory in
`Stilt.Memory` implement places. `Stilt.Paths` proves their laws.
-/

namespace Stilt

/-- A float: an `f32`, IEEE 754 binary32, or an `f64`, binary64, as Lean's
`Float32` and `Float` are, rounded to nearest with ties to even (numbers.ieee-754). -/
inductive FloatVal where
  | f32 (x : Float32)
  | f64 (x : Float)

/-- The type of a float. -/
def FloatVal.type : FloatVal → FloatTy
  | .f32 _ => .f32
  | .f64 _ => .f64

/-- A projection whose index has been evaluated (values.index-reads). -/
inductive Step where
  | field (name : Name)
  | index (index : Int)
  deriving DecidableEq, Repr

/-- The steps from a value to one of its parts. -/
abbrev Path := List Step

/-- Run-time values. An integer is the same value at every integer type that
holds it (numbers.numeric-types). A record keeps its fields in the order they are declared
(values.left-to-right). A closure holds copies of the variables it captured (expressions.capture). A function declared at the top level keeps the instantiation of its
type parameters and row variables, which a call applies to its body. A handle
names the cell of the store that holds its shared value by the cell's type and its
place among the cells of that type (shared.std-sync and `Stilt.World`). A window
reads a part of a source that the model of windows keeps in its store. -/
inductive Value where
  | int (value : Int)
  | float (value : FloatVal)
  | bool (value : Bool)
  | str (value : String)
  | unit
  | record (type : Name) (fields : List (Name × Value))
  | variant (type : Name) (ctor : Name) (payload : List Value)
  | list (elems : List Value)
  | closure (captured : List (Name × Value)) (params : List Param) (result : Ty)
      (row : Row) (body : Expr)
  | function (name : Name) (types : List Ty) (rows : List Row)
  | handle (type : Ty) (index : Nat)
  /-- A window into a part of the value at a location of the store: the part at
  `path`, sliced by each range in turn, as `View.of` and `view` slice
  (views.what-view-is and views.making-view). Only the model of windows makes one
  (`Stilt.Windows`). -/
  | window (loc : Nat) (path : Path) (ranges : List (Int × Int))

/-- The name of a tuple's record, which no declaration names. -/
def tupleName : Name := "(,)"

/-- A tuple of values: the record of its elements, each named by its position
(types.field-access). -/
def Value.tuple (vs : List Value) : Value := .record tupleName (positions vs)

/-- A value as an integer: itself when it is one, and 0 otherwise. -/
def Value.intOr : Value → Int
  | .int n => n
  | _ => 0

theorem mem_positionsFrom {α : Type} {i : Nat} :
    ∀ {xs : List α} {p : Name × α}, p ∈ positionsFrom i xs → p.2 ∈ xs
  | [], _, h => nomatch h
  | x :: xs, p, h => by
    rcases List.mem_cons.1 h with rfl | h
    · exact List.mem_cons_self
    · exact List.mem_cons_of_mem _ (mem_positionsFrom h)

/-- Why an evaluation stopped without a value or a raise: a panic, or a state
that no well-typed program reaches, such as reading a field of an integer. -/
inductive Fault where
  | panic (kind : PanicKind)
  | stuck
  deriving DecidableEq, Repr

/-- Replaces the value of the first pair with the key `k`, the one that
`List.lookup` finds. -/
def assocSet {β : Type} : List (Name × β) → Name → β → List (Name × β)
  | [], _, _ => []
  | (k', b') :: l, k, b => if k = k' then (k', b) :: l else (k', b') :: assocSet l k b

/-- The element of a list at an index, if `0 ≤ i < len` (std.lists). -/
def elemAt? (vs : List Value) (i : Int) : Option Value :=
  if 0 ≤ i then vs[i.toNat]? else none

namespace Value

/-- The part of a value at a path. An index out of bounds panics with the kind
`bounds` (effects.panic-kinds; std.lists). -/
def get : Value → Path → Except Fault Value
  | v, [] => .ok v
  | .record _ fields, .field f :: path =>
    match fields.lookup f with
    | some v => v.get path
    | none => .error .stuck
  | .list vs, .index i :: path =>
    match elemAt? vs i with
    | some v => v.get path
    | none => .error (.panic .bounds)
  | _, _ :: _ => .error .stuck

/-- The value with its part at a path replaced, as an assignment to a place
does (values.let-and-var). -/
def set : Value → Path → Value → Except Fault Value
  | _, [], w => .ok w
  | .record R fields, .field f :: path, w =>
    match fields.lookup f with
    | some v => (fun v' => .record R (assocSet fields f v')) <$> v.set path w
    | none => .error .stuck
  | .list vs, .index i :: path, w =>
    match elemAt? vs i with
    | some v => (fun v' => .list (vs.set i.toNat v')) <$> v.set path w
    | none => .error (.panic .bounds)
  | _, _ :: _, _ => .error .stuck

end Value

/-- Two paths reach disjoint parts of any value: at the first step where they
differ, they take different fields or different indexes. Neither is a prefix
of the other. -/
def Path.Disjoint : Path → Path → Prop
  | s :: p, t :: q => s ≠ t ∨ Path.Disjoint p q
  | _, _ => False

/-! ## Lemmas -/

section Assoc

variable {β : Type}

theorem lookup_cons_ne {l : List (Name × β)} {k j : Name} {b : β} (h : j ≠ k) :
    ((k, b) :: l).lookup j = l.lookup j := by
  have hjk : (j == k) = false := by simp [h]
  simp [List.lookup_cons, hjk]

theorem lookup_assocSet_self (l : List (Name × β)) (k : Name) (b : β)
    (h : (l.lookup k).isSome = true) : (assocSet l k b).lookup k = some b := by
  induction l with
  | nil => simp at h
  | cons kb l ih =>
    obtain ⟨k', b'⟩ := kb
    by_cases hk : k = k'
    · subst hk
      simp [assocSet]
    · rw [lookup_cons_ne hk] at h
      simp [assocSet, hk, lookup_cons_ne hk, ih h]

theorem lookup_assocSet_ne (l : List (Name × β)) {k j : Name} (b : β) (h : j ≠ k) :
    (assocSet l k b).lookup j = l.lookup j := by
  induction l with
  | nil => rfl
  | cons kb l ih =>
    obtain ⟨k', b'⟩ := kb
    by_cases hk : k = k'
    · subst hk
      simp [assocSet, lookup_cons_ne h]
    · by_cases hj : j = k'
      · subst hj
        simp [assocSet, hk]
      · simp [assocSet, hk, lookup_cons_ne hj, ih]

/-- Setting a key to the value it already has changes nothing. -/
theorem assocSet_of_lookup (l : List (Name × β)) (k : Name) (b : β)
    (h : l.lookup k = some b) : assocSet l k b = l := by
  induction l with
  | nil => rfl
  | cons kb l ih =>
    obtain ⟨k', b'⟩ := kb
    by_cases hk : k = k'
    · subst hk
      simp only [List.lookup_cons_self, Option.some.injEq] at h
      simp [assocSet, h]
    · rw [lookup_cons_ne hk] at h
      simp [assocSet, hk, ih h]

theorem assocSet_assocSet_self (l : List (Name × β)) (k : Name) (b b' : β) :
    assocSet (assocSet l k b) k b' = assocSet l k b' := by
  induction l with
  | nil => rfl
  | cons kb l ih =>
    obtain ⟨k', b''⟩ := kb
    by_cases hk : k = k'
    · subst hk
      simp [assocSet]
    · simp [assocSet, hk, ih]

theorem assocSet_comm (l : List (Name × β)) {k j : Name} (b c : β) (h : k ≠ j) :
    assocSet (assocSet l k b) j c = assocSet (assocSet l j c) k b := by
  induction l with
  | nil => rfl
  | cons kb l ih =>
    obtain ⟨k', b'⟩ := kb
    by_cases hk : k = k'
    · subst hk
      simp [assocSet, Ne.symm h]
    · by_cases hj : j = k'
      · subst hj
        simp [assocSet, hk]
      · simp [assocSet, hk, hj, ih]

end Assoc

theorem elemAt?_set_self {vs : List Value} {i : Int} {v : Value}
    (h : elemAt? vs i = some v) (w : Value) : elemAt? (vs.set i.toNat w) i = some w := by
  unfold elemAt? at h ⊢
  split at h
  · rename_i hi
    simp only [hi, ite_true]
    exact List.getElem?_set_self (List.getElem?_eq_some_iff.1 h).1
  · cases h

theorem elemAt?_set_ne {vs : List Value} {i j : Int} (w : Value) (hi : 0 ≤ i)
    (h : i ≠ j) : elemAt? (vs.set i.toNat w) j = elemAt? vs j := by
  unfold elemAt?
  split
  · have : i.toNat ≠ j.toNat := by omega
    rw [List.getElem?_set_ne this]
  · rfl

theorem set_of_elemAt? {vs : List Value} {i : Int} {v : Value}
    (h : elemAt? vs i = some v) : vs.set i.toNat v = vs := by
  unfold elemAt? at h
  split at h
  · obtain ⟨hlt, rfl⟩ := List.getElem?_eq_some_iff.1 h
    exact List.set_getElem_self hlt
  · cases h

theorem nonneg_of_elemAt? {vs : List Value} {i : Int} {v : Value}
    (h : elemAt? vs i = some v) : 0 ≤ i := by
  unfold elemAt? at h
  split at h
  · assumption
  · cases h

end Stilt
