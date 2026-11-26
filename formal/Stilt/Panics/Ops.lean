import Stilt.Ops

/-!
# Operations that can't panic

Which of the calculus's operations add the implicit effect `panic`
(effects.panicking-operations and effects.panic-kinds): `/` and `%` but by a
divisor written as a literal other than zero, `div_euclid` and `rem_euclid`,
slicing a string or a list, inserting into a list or removing from it, reading
a map's key, and `panic(msg)`, `unreachable()` and the other panics written
out. Every other operation ends with its value, with a panic of the kind
`overflow`, which `without panic` doesn't rule out (effects.without-overflow),
or stuck, which typing rules out (`Op.apply_calm`).
-/

namespace Stilt

/-- A result that is no panic but one of the kind `overflow`, and that only when `ov`
allows it: `Calm x false` is a result that is no panic at all. -/
def Calm {α : Type} (x : Except Fault α) (ov : Bool := true) : Prop :=
  ∀ k, x = .error (.panic k) → k = .overflow ∧ ov = true

namespace Calm

variable {α β : Type} {ov : Bool}

theorem ok (a : α) : Calm (Except.ok a : Except Fault α) ov := fun _ h => by cases h

theorem stuck : Calm (Except.error .stuck : Except Fault α) ov := fun _ h => by cases h

theorem overflow : Calm (Except.error (.panic .overflow) : Except Fault α) := fun _ h => by
  cases h; exact ⟨rfl, rfl⟩

/-- A result that is no panic at all is calm whatever `ov` allows. -/
theorem weaken {x : Except Fault α} (h : Calm x false) : Calm x ov := fun k hk => by
  have := (h k hk).2
  cases this

/-- A result calm with overflow, where `ov` allows it. -/
theorem allowing {x : Except Fault α} (h : Calm x) (hov : ov = true) : Calm x ov := by
  subst hov; exact h

theorem map {x : Except Fault α} (f : α → β) (h : Calm x ov) : Calm (f <$> x) ov := fun k hk => by
  cases x with
  | ok a => cases hk
  | error e => exact h k (by simpa [Functor.map, Except.map] using hk)

theorem ite {c : Prop} [Decidable c] {x y : Except Fault α} (hx : Calm x ov) (hy : Calm y ov) :
    Calm (if c then x else y) ov := by
  split
  · exact hx
  · exact hy

theorem check (k : IntTy) (n : Int) : Calm (k.check n) := by
  unfold IntTy.check
  exact ite (ok _) overflow

theorem shift (k : IntTy) (o : Shift) (a b : Int) : Calm (k.shift o a b) := by
  unfold IntTy.shift
  exact ite overflow (ok _)

theorem orStuck (o : Option α) : Calm (Stilt.orStuck o) ov := by
  cases o
  · exact stuck
  · exact ok _

theorem onList {l : Value} {f : List Value → Except Fault Value} (h : ∀ xs, Calm (f xs) ov) :
    Calm (Stilt.onList l f) ov := by
  unfold Stilt.onList; split
  · exact h _
  · exact stuck

theorem onMap {m : Value} {f : List (Value × Value) → Option Value → Except Fault Value}
    (h : ∀ es d, Calm (f es d) ov) : Calm (Stilt.onMap m f) ov := by
  unfold Stilt.onMap; split
  · exact h _ _
  · exact stuck

theorem onSet {s : Value} {f : List Value → Except Fault Value} (h : ∀ ks, Calm (f ks) ov) :
    Calm (Stilt.onSet s f) ov := by
  unfold Stilt.onSet; split
  · exact h _
  · exact stuck

end Calm

/-- A result that is no panic, and whose value `P` holds of. -/
def CalmTo {α : Type} (P : α → Prop) (x : Except Fault α) : Prop :=
  Calm x false ∧ ∀ a, x = .ok a → P a

namespace CalmTo

variable {α β : Type} {P : α → Prop} {Q : β → Prop}

theorem ok {a : α} (h : P a) : CalmTo P (.ok a) := ⟨Calm.ok a, fun _ h' => by cases h'; exact h⟩

theorem stuck : CalmTo P (.error .stuck) := ⟨Calm.stuck, fun _ h => by cases h⟩

theorem bind {x : Except Fault α} {f : α → Except Fault β} (hx : CalmTo P x)
    (hf : ∀ a, P a → CalmTo Q (f a)) : CalmTo Q (x >>= f) := by
  cases x with
  | error e => exact ⟨fun k hk => hx.1 k (by cases hk; rfl), fun _ h => by cases h⟩
  | ok a => exact hf a (hx.2 a rfl)

theorem map {x : Except Fault α} {f : α → β} (hx : CalmTo P x) (hf : ∀ a, P a → Q (f a)) :
    CalmTo Q (f <$> x) := by
  cases x with
  | error e => exact ⟨fun k hk => hx.1 k (by cases hk; rfl), fun _ h => by cases h⟩
  | ok a => exact ok (hf a (hx.2 a rfl))

end CalmTo

/-- Closes a goal `Calm x` whose `x` is built of values, overflow checks and
matches on operands. -/
macro "calm" : tactic => `(tactic| repeat (first
  | exact Calm.ok _
  | exact Calm.stuck
  | exact Calm.overflow
  | exact Calm.check _ _
  | exact Calm.shift _ _ _ _
  | exact Calm.orStuck _
  | apply Calm.map
  | (apply Calm.onList; intro)
  | (apply Calm.onMap; intro _ _)
  | (apply Calm.onSet; intro)
  | split))

/-- `/`, `%`, `div_euclid` and `rem_euclid`, which panic on a divisor of zero. -/
def Arith.divides : Arith → Bool
  | .div | .rem => true
  | _ => false

def IntMethod.divides : IntMethod → Bool
  | .divEuclid | .remEuclid => true
  | _ => false

/-- `+`, `-` and `*` can only overflow. -/
theorem IntTy.arith_calm (k : IntTy) {o : Arith} (ho : o.divides = false) (a b : Int) :
    Calm (k.arith o a b) := by
  cases o
  · exact Calm.check k _
  · exact Calm.check k _
  · exact Calm.check k _
  · cases ho
  · cases ho

/-- `/` and `%` by a divisor other than zero can only overflow. -/
theorem IntTy.arith_calm_of_ne (k : IntTy) (o : Arith) (a : Int) {b : Int} (hb : b ≠ 0) :
    Calm (k.arith o a b) := by
  cases o
  · exact Calm.check k _
  · exact Calm.check k _
  · exact Calm.check k _
  · simp only [IntTy.arith, hb, ↓reduceIte]; exact Calm.check k _
  · simp only [IntTy.arith, hb, ↓reduceIte]
    exact Calm.ite (Calm.ok _) Calm.overflow

/-- The methods of integer types but `div_euclid` and `rem_euclid` can only overflow. -/
theorem IntTy.method_calm (k : IntTy) {m : IntMethod} (hm : m.divides = false)
    (a b : Int) : Calm (k.method m a b) := by
  cases m <;> simp only [IntTy.method] <;>
    first
    | exact absurd hm (by decide)
    | exact Calm.check _ _
    | (split
       · exact Calm.check _ _
       · exact Calm.ite Calm.overflow (Calm.check _ _))

/-- `div_euclid` and `rem_euclid` by a divisor other than zero can only overflow. -/
theorem IntTy.method_calm_of_ne (k : IntTy) (m : IntMethod) (a : Int) {b : Int} (hb : b ≠ 0) :
    Calm (k.method m a b) := by
  cases m <;> simp only [IntTy.method] <;>
    first
    | exact Calm.check _ _
    | (split
       · exact Calm.check _ _
       · exact Calm.ite Calm.overflow (Calm.check _ _))
    | (simp only [IntTy.euclid, hb, ↓reduceIte]; exact Calm.ite Calm.overflow (Calm.check _ _))

/-- Whether a function of lists can't panic: every one but `slice`, `insert` and
`remove`, which panic out of bounds (std.lists). -/
def ListOp.panicFree : ListOp → Bool
  | .slice | .insert | .removeAt => false
  | _ => true

theorem ListOp.apply_calm {l : ListOp} (hl : l.panicFree = true) (vs : List Value) :
    Calm (l.apply vs) := by
  unfold ListOp.apply
  split <;> first | (simp [ListOp.panicFree] at hl; done) | calm

/-- Whether a function of maps can't panic: every one but `m[k]`, which panics on a
missing key (std.maps). -/
def MapOp.panicFree : MapOp → Bool
  | .index => false
  | _ => true

theorem MapOp.apply_calm {m : MapOp} (hm : m.panicFree = true) (vs : List Value) :
    Calm (m.apply vs) := by
  unfold MapOp.apply
  split <;> first | (simp [MapOp.panicFree] at hm; done) | calm

theorem SetOp.apply_calm (m : SetOp) (vs : List Value) : Calm (m.apply vs) := by
  unfold SetOp.apply
  split <;> calm

/-- Whether an operation can't panic, but with `overflow` (effects.panicking-operations). -/
def Op.panicFree : Op → Bool
  | .arith o _ => !o.divides
  | .intMethod m _ => !m.divides
  | .slice | .view | .panic _ => false
  | .list l => l.panicFree
  | .map m => m.panicFree
  | _ => true

theorem Op.compute_calm {o : Op} (ho : o.panicFree = true) (ss : List Scalar) :
    Calm (o.compute ss) := by
  unfold Op.compute
  split <;> first
    | (simp [Op.panicFree] at ho; done)
    | exact Calm.map _ (IntTy.arith_calm _ (by simpa [Op.panicFree] using ho) _ _)
    | exact Calm.map _ (IntTy.method_calm _ (by simpa [Op.panicFree] using ho) _ _)
    | (simp only [Str.len]; calm)
    | calm

theorem Op.apply_calm {o : Op} (ho : o.panicFree = true) (vs : List Value) :
    Calm (o.apply vs) := by
  unfold Op.apply
  split
  · exact Calm.ok _
  · calm
  · simp [Op.panicFree] at ho
  · calm
  · calm
  · calm
  · exact ListOp.apply_calm (by simpa [Op.panicFree] using ho) vs
  · exact MapOp.apply_calm (by simpa [Op.panicFree] using ho) vs
  · exact SetOp.apply_calm _ vs
  · simp [Op.panicFree] at ho
  · split
    · exact Calm.ok _
    · exact Calm.stuck
  · unfold Op.applyScalars
    split
    · exact Calm.map _ (Op.compute_calm ho _)
    · exact Calm.stuck

/-- `/`, `%`, `div_euclid` and `rem_euclid` by a divisor written as a literal other
than zero can only overflow (effects.panicking-operations). -/
theorem Op.apply_calm_divisor {o : Op} (ho : (∃ a k, o = .arith a k) ∨ ∃ m k, o = .intMethod m k)
    (v : Value) {n : Int} (hn : n ≠ 0) : Calm (o.apply [v, .int n]) := by
  rcases ho with ⟨a, k, rfl⟩ | ⟨m, k, rfl⟩ <;> cases v <;>
    first
    | exact Calm.stuck
    | exact Calm.map _ Calm.stuck
    | exact Calm.map _ (Calm.map _ (IntTy.arith_calm_of_ne _ _ _ hn))
    | exact Calm.map _ (Calm.map _ (IntTy.method_calm_of_ne _ _ _ hn))

end Stilt
