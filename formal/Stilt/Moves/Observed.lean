import Stilt.Moves.Erase
import Stilt.Semantics

/-!
# Erasing the marks of values

A closure value holds its body, so the marks of a body reach the values that a
run makes, and through them its observation. `Value.erase` reads every mark
of a value's closures as a variable, at every depth: a value of the marked
program becomes the value that its erasure makes. Reading and writing a place
commute with it, so copy-in, copy-out's frames can be erased as they run
(`Stilt.Moves.Oracle`).
-/

namespace Stilt

mutual

/-- A value with every mark in the bodies of its closures read as a variable,
captured values included (values.passing-values; expressions.capture). -/
def Value.erase : Value → Value
  | .int n => .int n
  | .float x => .float x
  | .str s => .str s
  | .bool b => .bool b
  | .unit => .unit
  | .record R fields => .record R (eraseBindings fields)
  | .variant T C vs => .variant T C (eraseValues vs)
  | .list vs => .list (eraseValues vs)
  | .closure captured ps r ρ body => .closure (eraseBindings captured) ps r ρ body.erase
  | .function f types rows => .function f types rows
  | .handle u k => .handle u k
  | .window l p r => .window l p r

/-- Erases the marks of a list of values (values.passing-values). -/
def eraseValues : List Value → List Value
  | [] => []
  | v :: vs => v.erase :: eraseValues vs

/-- Erases the marks of named values: a record's fields, a closure's captured
variables, or a copy frame (values.passing-values). -/
def eraseBindings : List (Name × Value) → List (Name × Value)
  | [] => []
  | (x, v) :: l => (x, v.erase) :: eraseBindings l

end

/-- An argument once evaluated, with its marks erased: the last use of a
variable is passed as its value, as the erasure's argument passes it, and a
place has no value to erase (values.passing-values and values.inout-argument-order). -/
def Passed.erase : Passed → Passed
  | .value v | .moved _ v => .value v.erase
  | .place x p => .place x p

/-- A jump with the marks of a `return`'s value erased. -/
def Jump.erase : Jump → Jump
  | .ret v => .ret v.erase
  | j => j

/-- What a run shows, with the marks of the values it shows erased (values.passing-values). -/
def Observation.erase : Observation → Observation
  | .returned v => .returned v.erase
  | .raised e => .raised e.erase
  | .jumped j => .jumped j.erase
  | o => o

/-- What a run shows, with the marks of the error it raises erased and every
other observation as it is (values.passing-values). A well-typed program returns `()`
(program.main), which has no marks to erase. -/
def Observation.eraseRaised : Observation → Observation
  | .raised e => .raised e.erase
  | o => o

/-- Only `()` erases to `()`. -/
theorem Value.erase_eq_unit {v : Value} : v.erase = .unit ↔ v = .unit := by
  cases v <;> simp [Value.erase]

/-! ## Lists and frames -/

theorem eraseBindings_positionsFrom (i : Nat) :
    ∀ vs : List Value, eraseBindings (positionsFrom i vs) = positionsFrom i (eraseValues vs)
  | [] => rfl
  | v :: vs => by
    simp [positionsFrom, eraseBindings, eraseValues, eraseBindings_positionsFrom (i + 1) vs]

theorem Value.scalar?_erase : ∀ v : Value, v.erase.scalar? = v.scalar?
  | .int _ | .float _ | .bool _ | .str _ | .unit | .record .. | .variant .. | .list _ | .closure ..
  | .function .. | .handle .. | .window .. => rfl

theorem Scalar.erase_value : ∀ s : Scalar, s.value.erase = s.value
  | .int _ | .float _ | .bool _ | .str _ => rfl

theorem mapM_scalar?_erase :
    ∀ vs : List Value, (eraseValues vs).mapM Value.scalar? = vs.mapM Value.scalar?
  | [] => rfl
  | v :: vs => by simp [eraseValues, Value.scalar?_erase v, mapM_scalar?_erase vs]

theorem length_eraseValues : ∀ vs : List Value, (eraseValues vs).length = vs.length
  | [] => rfl
  | _ :: vs => by simp [eraseValues, length_eraseValues vs]

theorem lookup_eraseBindings (x : Name) :
    ∀ l : List (Name × Value), (eraseBindings l).lookup x = (l.lookup x).map Value.erase
  | [] => rfl
  | (y, v) :: l => by
    by_cases h : x = y
    · subst h
      simp [eraseBindings]
    · simp [eraseBindings, lookup_cons_ne h, lookup_eraseBindings x l]

theorem assocSet_eraseBindings (x : Name) (v : Value) :
    ∀ l : List (Name × Value),
      assocSet (eraseBindings l) x v.erase = eraseBindings (assocSet l x v)
  | [] => rfl
  | (y, w) :: l => by
    by_cases h : x = y
    · subst h
      simp [eraseBindings, assocSet]
    · simp [eraseBindings, assocSet, h, assocSet_eraseBindings x v l]

theorem zip_eraseValues : ∀ (xs : List Name) (vs : List Value),
    xs.zip (eraseValues vs) = eraseBindings (xs.zip vs)
  | [], _ | _ :: _, [] => rfl
  | x :: xs, v :: vs => by simp [eraseValues, eraseBindings, zip_eraseValues xs vs]

theorem getElem?_eraseValues : ∀ (vs : List Value) (n : Nat),
    (eraseValues vs)[n]? = vs[n]?.map Value.erase
  | [], _ => rfl
  | _ :: _, 0 => rfl
  | _ :: vs, n + 1 => by simp [eraseValues, getElem?_eraseValues vs n]

theorem elemAt?_eraseValues (vs : List Value) (i : Int) :
    elemAt? (eraseValues vs) i = (elemAt? vs i).map Value.erase := by
  unfold elemAt?
  split <;> simp [getElem?_eraseValues]

theorem set_eraseValues (v : Value) : ∀ (vs : List Value) (n : Nat),
    (eraseValues vs).set n v.erase = eraseValues (vs.set n v)
  | [], _ => rfl
  | _ :: _, 0 => rfl
  | w :: vs, n + 1 => by simp [eraseValues, set_eraseValues v vs n]

/-! ## Reading and writing -/

/-- Reading along a path commutes with erasure. -/
theorem Value.get_erase : ∀ (v : Value) (p : Path), v.erase.get p = (v.get p).map Value.erase
  | _, [] => rfl
  | .record R fields, .field f :: p => by
    simp only [Value.erase, Value.get, lookup_eraseBindings]
    cases fields.lookup f with
    | none => rfl
    | some u => exact Value.get_erase u p
  | .list vs, .index i :: p => by
    simp only [Value.erase, Value.get, elemAt?_eraseValues]
    cases elemAt? vs i with
    | none => rfl
    | some u => exact Value.get_erase u p
  | .record .., .index _ :: _ | .list _, .field _ :: _ | .int _, _ :: _ | .float _, _ :: _
  | .bool _, _ :: _ | .str _, _ :: _
  | .unit, _ :: _ | .variant .., _ :: _ | .closure .., _ :: _ | .function .., _ :: _ | .handle .., _ :: _
  | .window .., _ :: _ => by
    simp [Value.erase, Value.get, Except.map]

/-- Writing along a path commutes with erasure. -/
theorem Value.set_erase : ∀ (v : Value) (p : Path) (w : Value),
    v.erase.set p w.erase = (v.set p w).map Value.erase
  | _, [], _ => rfl
  | .record R fields, .field f :: p, w => by
    simp only [Value.erase, Value.set, lookup_eraseBindings]
    cases fields.lookup f with
    | none => rfl
    | some u =>
      simp only [Option.map_some, Value.set_erase u p w]
      cases u.set p w <;>
        simp [Except.map, Functor.map, Value.erase, assocSet_eraseBindings]
  | .list vs, .index i :: p, w => by
    simp only [Value.erase, Value.set, elemAt?_eraseValues]
    cases elemAt? vs i with
    | none => rfl
    | some u =>
      simp only [Option.map_some, Value.set_erase u p w]
      cases u.set p w <;> simp [Except.map, Functor.map, Value.erase, set_eraseValues]
  | .record .., .index _ :: _, _ | .list _, .field _ :: _, _ | .int _, _ :: _, _
  | .float _, _ :: _, _ | .str _, _ :: _, _
  | .bool _, _ :: _, _ | .unit, _ :: _, _ | .variant .., _ :: _, _ | .closure .., _ :: _, _
  | .function .., _ :: _, _ | .handle .., _ :: _, _ | .window .., _ :: _, _ => by
    simp [Value.erase, Value.set, Except.map]

/-- Reading a place of an erased frame reads the erased value. -/
theorem Copy.read_erase (fr : Copy.Frame) (x : Name) (p : Path) :
    Copy.read (eraseBindings fr) x p = (Copy.read fr x p).map Value.erase := by
  unfold Copy.read
  rw [lookup_eraseBindings]
  cases fr.lookup x with
  | none => rfl
  | some v => exact Value.get_erase v p

/-- Writing a place of an erased frame writes the erased value. -/
theorem Copy.write_erase (fr : Copy.Frame) (x : Name) (p : Path) (w : Value) :
    Copy.write (eraseBindings fr) x p w.erase = (Copy.write fr x p w).map eraseBindings := by
  unfold Copy.write
  rw [lookup_eraseBindings]
  cases fr.lookup x with
  | none => rfl
  | some v =>
    simp only [Option.map_some, Value.set_erase]
    cases v.set p w <;> simp [Except.map, Functor.map, assocSet_eraseBindings]

theorem newestOf_eraseBindings :
    ∀ (keep : Name → Bool) (c : List (Name × Value)),
      newestOf keep (eraseBindings c) = eraseBindings (newestOf keep c)
  | _, [] => rfl
  | keep, (x, v) :: c => by
    by_cases h : keep x = true <;>
      simp [eraseBindings, newestOf, h, newestOf_eraseBindings _ c]

/-- A closure literal with its marks erased captures, of the erased variables in scope,
the erasures of those it captures (expressions.capture). -/
theorem captureOf_erase (ps : List Param) (body : Expr) (c : List (Name × Value)) :
    captureOf ps body.erase (eraseBindings c) = eraseBindings (captureOf ps body c) := by
  simp only [captureOf, Expr.captures_erase, newestOf_eraseBindings]

end Stilt
