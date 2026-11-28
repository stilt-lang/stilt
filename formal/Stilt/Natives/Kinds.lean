import Stilt.Ops

/-!
# The panics of the natives

The kinds of panic each native of the calculus may end with, as its paragraph names them
(std.no-panics-by-default), and the lemmas that bound the integers the natives that count
check against `i64`: a count of a string's scalar values or of a substring's occurrences, and
the offset `find` gives, are no greater than the string's length.
-/

namespace Stilt

/-- The kinds of panic of a method of an integer type (std.integers): `abs`, `pow`, `gcd` and
`lcm` panic with `overflow` when their result doesn't fit, and `div_euclid` and `rem_euclid`
with `divide-by-zero` by 0 and with `overflow` for `T.MIN` by `-1`. The others never panic. -/
def IntMethod.panicKinds : IntMethod → List PanicKind
  | .abs | .pow | .gcd | .lcm => [.overflow]
  | .divEuclid | .remEuclid => [.divideByZero, .overflow]
  | _ => []

/-- The kinds of panic of a function of lists: `slice`, `insert` and `remove` panic with
`bounds` (std.lists). The others never panic. -/
def ListOp.panicKinds : ListOp → List PanicKind
  | .slice | .insert | .removeAt => [.bounds]
  | _ => []

/-- The kinds of panic of a function of maps: `m[k]` panics with `missing-key` (std.maps). The
others never panic. -/
def MapOp.panicKinds : MapOp → List PanicKind
  | .index => [.missingKey]
  | _ => []

/-- The kinds of panic each native of the calculus may end with, those its paragraph names:
`overflow` for unary `-`, `+`, `-`, `*` and the shifts, and `divide-by-zero` too for `/` and `%`
(numbers.integer-panics); those of the integer methods, lists and maps; `bounds` and
`utf8-boundary` for slicing a string, or viewing a part of one; and for `panic(msg)`,
`unreachable()` and the other panics written out, their own kind. Every other native, a float's
methods, the natives of strings but `slice`, sets, conversions and the operations on the world
included, never panics. -/
def Op.panicKinds : Op → List PanicKind
  | .neg _ | .shift .. => [.overflow]
  | .arith .div _ | .arith .rem _ => [.divideByZero, .overflow]
  | .arith _ _ => [.overflow]
  | .intMethod m _ => m.panicKinds
  | .slice | .view => [.bounds, .utf8Boundary]
  | .list l => l.panicKinds
  | .map m => m.panicKinds
  | .panic k => [k]
  | _ => []

/-- A string whose length in bytes, read as the natives read it, and whose number of scalar
values are below `i64.MAX`, as every string a machine holds is. -/
def Str.Fits (s : String) : Prop :=
  (s.utf8ByteSize : Int) ≤ IntTy.i64.max ∧ (s.length : Int) < IntTy.i64.max ∧
    (s.toUTF8.toList.length : Int) ≤ IntTy.i64.max

/-- A value whose length, as a list, a map, a set or a string, fits in `i64`, as every value
a machine holds does. -/
def Value.Fits (v : Value) : Prop :=
  (∀ xs, v.list? = some xs → (xs.length : Int) ≤ IntTy.i64.max) ∧
  (∀ es d, v.map? = some (es, d) → (es.length : Int) ≤ IntTy.i64.max) ∧
  (∀ ks, v.set? = some ks → (ks.length : Int) ≤ IntTy.i64.max) ∧
  (∀ s, v = .str s → Str.Fits s)

/-- A scalar that fits, as a value. -/
def Scalar.Fits : Scalar → Prop
  | .str s => Str.Fits s
  | _ => True

/-- A result that is no panic but one of the kinds `ks`. -/
def PanicsWith {α : Type} (ks : List PanicKind) (x : Except Fault α) : Prop :=
  ∀ k, x = .error (.panic k) → k ∈ ks

namespace PanicsWith

variable {α β : Type} {ks : List PanicKind}

theorem ok (a : α) : PanicsWith ks (.ok a : Except Fault α) := fun _ h => by cases h

theorem stuck : PanicsWith ks (.error .stuck : Except Fault α) := fun _ h => by cases h

theorem panic {k : PanicKind} (h : k ∈ ks) : PanicsWith ks (.error (.panic k) : Except Fault α) :=
  fun _ h' => by cases h'; exact h

theorem mono {ks' : List PanicKind} {x : Except Fault α} (h : PanicsWith ks x) (hs : ks ⊆ ks') :
    PanicsWith ks' x := fun k hk => hs (h k hk)

theorem map {x : Except Fault α} (f : α → β) (h : PanicsWith ks x) : PanicsWith ks (f <$> x) :=
  fun k hk => by
    cases x with
    | ok a => cases hk
    | error e => exact h k (by simpa [Functor.map, Except.map] using hk)

theorem ite {c : Prop} [Decidable c] {x y : Except Fault α} (hx : PanicsWith ks x)
    (hy : PanicsWith ks y) : PanicsWith ks (if c then x else y) := by
  split
  · exact hx
  · exact hy

theorem orStuck (o : Option α) : PanicsWith ks (Stilt.orStuck o) := by
  cases o
  · exact stuck
  · exact ok _

theorem check_mem (k : IntTy) (n : Int) (h : PanicKind.overflow ∈ ks) : PanicsWith ks (k.check n) :=
  by unfold IntTy.check; exact ite (ok _) (panic h)

theorem check_of {k : IntTy} {n : Int} (h : k.Contains n) : PanicsWith ks (k.check n) := by
  unfold IntTy.check; simp only [h, ↓reduceIte]; exact ok _

theorem within (k : IntTy) (a b : Int) {x : Except Fault Int}
    (h : k.Contains a → k.Contains b → PanicsWith ks x) : PanicsWith ks (k.within a b x) := by
  unfold IntTy.within
  split
  · rename_i hab; exact h hab.1 hab.2
  · exact stuck

theorem onList {l : Value} {f : List Value → Except Fault Value}
    (h : ∀ xs, l.list? = some xs → PanicsWith ks (f xs)) : PanicsWith ks (Stilt.onList l f) := by
  unfold Stilt.onList; split
  · rename_i hl; exact h _ hl
  · exact stuck

theorem onMap {m : Value} {f : List (Value × Value) → Option Value → Except Fault Value}
    (h : ∀ es d, m.map? = some (es, d) → PanicsWith ks (f es d)) :
    PanicsWith ks (Stilt.onMap m f) := by
  unfold Stilt.onMap; split
  · rename_i hm; exact h _ _ hm
  · exact stuck

theorem onSet {s : Value} {f : List Value → Except Fault Value}
    (h : ∀ es, s.set? = some es → PanicsWith ks (f es)) : PanicsWith ks (Stilt.onSet s f) := by
  unfold Stilt.onSet; split
  · rename_i hs; exact h _ hs
  · exact stuck

end PanicsWith

/-- A count that fits in `i64` is an `i64`. -/
theorem i64_contains {n : Nat} (h : (n : Int) ≤ IntTy.i64.max) : IntTy.i64.Contains n :=
  ⟨by have := IntTy.min_le_zero .i64; omega, h⟩

theorem IntTy.bits_le (k : IntTy) : k.bits ≤ 64 := by cases k <;> decide

theorem i64_contains_le_bits {n : Nat} (k : IntTy) (h : n ≤ k.bits) : IntTy.i64.Contains n :=
  i64_contains (by have := k.bits_le; simp only [IntTy.max, IntTy.signed, IntTy.bits]; omega)

/-- The offset of the first place where `sub` starts is within the bytes. -/
theorem Str.firstAt_le (sub : List UInt8) :
    ∀ (bs : List UInt8) (i n : Nat), Str.firstAt sub bs i = some n → n ≤ i + bs.length
  | [], i, n, h => by
    unfold Str.firstAt at h; split at h
    · cases h; simp
    · cases h
  | b :: bs, i, n, h => by
    unfold Str.firstAt at h; split at h
    · cases h; simp
    · have := Str.firstAt_le sub bs (i + 1) n h; simp only [List.length_cons]; omega

/-- The offset of the last place where `sub` starts is within the bytes. -/
theorem Str.lastAt_le (sub : List UInt8) :
    ∀ (bs : List UInt8) (i n : Nat), Str.lastAt sub bs i = some n → n ≤ i + bs.length
  | [], i, n, h => by
    unfold Str.lastAt at h; split at h
    · cases h; simp
    · cases h
  | b :: bs, i, n, h => by
    unfold Str.lastAt at h; split at h
    · rename_i j hj
      have := Str.lastAt_le sub bs (i + 1) j hj
      have hjn : j = n := Option.some.inj h
      simp only [List.length_cons]; omega
    · split at h
      · cases h; simp
      · cases h

/-- `find` and `rfind` give an offset within the string's bytes. -/
theorem Str.find_le {last : Bool} {s sub : String} {n : Nat} (h : Str.find last s sub = some n) :
    n ≤ s.toUTF8.toList.length := by
  unfold Str.find at h
  cases last
  · have := Str.firstAt_le _ _ 0 n h; omega
  · have := Str.lastAt_le _ _ 0 n h; omega

/-- A count of occurrences is no greater than its fuel. -/
theorem Str.occurrences_le (pat : List Char) (n : Nat) (cs : List Char) :
    Str.occurrences pat n cs ≤ n := by
  induction n generalizing cs with
  | zero => cases cs <;> simp [Str.occurrences]
  | succ n ih =>
    cases cs with
    | nil => simp [Str.occurrences]
    | cons c cs =>
      simp only [Str.occurrences]
      split
      · have := ih (cs.drop (pat.length - 1)); omega
      · have := ih cs; omega

/-- `count` is at most the number of scalar values plus one. -/
theorem Str.count_le (s sub : String) : Str.count s sub ≤ s.length + 1 := by
  unfold Str.count
  split
  · exact Nat.le_refl _
  · have := Str.occurrences_le sub.toList s.length s.toList; omega

end Stilt
