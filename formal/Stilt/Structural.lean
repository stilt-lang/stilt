import Stilt.Maps

/-!
# Structural equality and order

What the prelude's structural impls of `Eq` and `Ord` compute (traits.structural-impls
and traits.structural-calls): equality compares the components from first to
last and stops at the first unequal pair, with different variants and lists of
different lengths unequal; order is lexicographic, a record's fields in
declaration order, a variant first by its constructor's place in its type's
declaration, then by its payload, and a shorter list before a longer one that
starts with it. `==` on a float is IEEE 754's, and `compare` its total order,
in which NaNs are equal and greatest and `-0.0` comes before `0.0`
(traits.floats). Maps, whose equality ignores the order of their entries
(traits.map-equality), are outside: the export compares only types without one.
-/

namespace Stilt

/-- Where a float stands in `compare`'s order: its bits read as a signed
magnitude, or nothing for a NaN, which is greater than every other value
(traits.floats). -/
def FloatVal.totalKey : FloatVal → Option Int
  | .f32 x => if x.isNaN then none else key 31 x.toBits.toNat
  | .f64 x => if x.isNaN then none else key 63 x.toBits.toNat
where
  key (sign : Nat) (b : Nat) : Option Int :=
    let magnitude := (b % 2 ^ sign : Nat)
    some (if b / 2 ^ sign % 2 = 1 then -(magnitude : Int) - 1 else magnitude)

/-- `compare` on floats (traits.floats). -/
def FloatVal.order (x y : FloatVal) : Ordering :=
  match x.totalKey, y.totalKey with
  | some a, some b => Ord.compare a b
  | some _, none => .lt
  | none, some _ => .gt
  | none, none => .eq

/-- The first of two orderings that isn't `eq`. -/
def _root_.Ordering.andThen (o : Ordering) (next : Ordering) : Ordering :=
  if o = .eq then next else o

/-- The constructors of each variant type, in declaration order. -/
abbrev CtorOrders := List (Name × List Name)

/-- Where a constructor stands in its type's declaration. -/
def CtorOrders.place (orders : CtorOrders) (T C : Name) : Nat :=
  ((orders.lookup T).getD []).idxOf C

mutual

/-- Structural equality (traits.structural-calls); two handles are equal when they name one
cell. -/
def Value.same : Value → Value → Bool
  | .int a, .int b => a == b
  | .float x, .float y => FloatVal.compare .eq x y == some true
  | .bool a, .bool b => a == b
  | .str s, .str t => s == t
  | .unit, .unit => true
  | .record _ fs, .record _ gs => sameFields fs gs
  | .variant _ C vs, .variant _ D ws => C == D && sameValues vs ws
  | .list vs, .list ws => sameValues vs ws
  | .handle u k, .handle u' k' => decide (u = u') && k == k'
  | _, _ => false

/-- Element by element, a list's length included. -/
def sameValues : List Value → List Value → Bool
  | [], [] => true
  | v :: vs, w :: ws => v.same w && sameValues vs ws
  | _, _ => false

/-- Field by field, in declaration order. -/
def sameFields : List (Name × Value) → List (Name × Value) → Bool
  | [], [] => true
  | (_, v) :: fs, (_, w) :: gs => v.same w && sameFields fs gs
  | _, _ => false

end

mutual

/-- Structural order (traits.structural-calls). -/
def Value.order (orders : CtorOrders) : Value → Value → Ordering
  | .int a, .int b => Ord.compare a b
  | .float x, .float y => x.order y
  | .bool a, .bool b => Ord.compare a b
  | .str s, .str t => Ord.compare s.toList t.toList
  | .unit, .unit => .eq
  | .record _ fs, .record _ gs => orderFields orders fs gs
  | .variant T C vs, .variant _ D ws =>
    (Ord.compare (orders.place T C) (orders.place T D)).andThen (orderValues orders vs ws)
  | .list vs, .list ws => orderValues orders vs ws
  | _, _ => .eq

/-- Lexicographically, a shorter list before a longer one that starts with it. -/
def orderValues (orders : CtorOrders) : List Value → List Value → Ordering
  | [], [] => .eq
  | [], _ :: _ => .lt
  | _ :: _, [] => .gt
  | v :: vs, w :: ws => (v.order orders w).andThen (orderValues orders vs ws)

/-- Field by field, in declaration order. -/
def orderFields (orders : CtorOrders) : List (Name × Value) → List (Name × Value) → Ordering
  | (_, v) :: fs, (_, w) :: gs => (v.order orders w).andThen (orderFields orders fs gs)
  | _, _ => .eq

end

/-- A comparison through the structural impls: `==` and `!=` by `Eq`, the
others by `Ord.compare` (traits.operators). -/
def Cmp.values (orders : CtorOrders) : Cmp → Value → Value → Bool
  | .eq, v, w => v.same w
  | .ne, v, w => !v.same w
  | .lt, v, w => v.order orders w = .lt
  | .le, v, w => v.order orders w ≠ .gt
  | .gt, v, w => v.order orders w = .gt
  | .ge, v, w => v.order orders w ≠ .lt

/-- Whether an element whose key is `k` may come before one whose key is `k'`:
when `k` orders at most `k'`, or at least it when the order is descending. -/
def keyBefore (orders : CtorOrders) (descending : Bool) (k k' : Value) : Bool :=
  if descending then k.order orders k' != .lt else k.order orders k' != .gt

/-- `xs` sorted stably by their keys `ks`, the `i`-th key that of the `i`-th
element: a merge sort keeps elements whose keys are equal in their order (std.lists). -/
def sortByKeys (orders : CtorOrders) (descending : Bool) (ks xs : List Value) : List Value :=
  ((ks.zip xs).mergeSort fun a b => keyBefore orders descending a.1 b.1).map Prod.snd

/-- A sorted list's elements are the list's. -/
theorem mem_sortByKeys {orders : CtorOrders} {descending : Bool} {ks xs : List Value} {v : Value}
    (h : v ∈ sortByKeys orders descending ks xs) : v ∈ xs := by
  obtain ⟨p, hp, rfl⟩ := List.mem_map.1 h
  exact (List.of_mem_zip ((List.mergeSort_perm _ _).mem_iff.1 hp)).2

end Stilt
