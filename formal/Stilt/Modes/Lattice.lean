import Stilt.Declarations

/-!
# The lattice of modes

The five axes of modes.bindings-and-axes, their points and their order, and the modes
of a binding: one point on each axis. A mode is a fact of a binding, never part
of a type (modes.fact-not-type), so nothing here touches `Stilt.Typing`: the typing
judgment reads no mode, and the model infers them from the elaborated syntax
(`Stilt.Modes.Facts`).

Each axis has two points, ordered as the record writes them. Inference finds
the least point each rule allows (modes.bindings-and-axes); `Axis.join` is how two reasons for a
point combine. The thread axes are settled here: no type of the calculus, as no
core type, is fixed or contended, so every binding is `portable` and `calm`
(modes.fixed-values, modes.contended-values and modes.mode-crossing).
-/

namespace Stilt

/-- An axis of modes.bindings-and-axes: two points, the least first. -/
class Axis (α : Type) where
  least : α
  greatest : α
  cases : ∀ a : α, a = least ∨ a = greatest
  distinct : least ≠ greatest

namespace Axis

variable {α : Type} [Axis α]

/-- The order of an axis: the least point is below the greatest. -/
def le (a b : α) : Prop := a = least ∨ b = greatest

/-- The point that two reasons give together: the greatest if either gives
it. -/
def join [DecidableEq α] (a b : α) : α :=
  if a = greatest ∨ b = greatest then greatest else least

theorem le_refl (a : α) : le a a := by
  rcases cases a with h | h
  · exact .inl h
  · exact .inr h

theorem le_trans {a b c : α} (h₁ : le a b) (h₂ : le b c) : le a c := by
  rcases h₁ with h | h
  · exact .inl h
  · rcases h₂ with h' | h'
    · exact absurd (h.symm.trans h') (Ne.symm distinct)
    · exact .inr h'

theorem le_antisymm {a b : α} (h₁ : le a b) (h₂ : le b a) : a = b := by
  rcases cases a with rfl | rfl <;> rcases cases b with rfl | rfl
  · rfl
  · rcases h₂ with h | h
    · exact absurd h.symm distinct
    · exact absurd h distinct
  · rcases h₁ with h | h
    · exact absurd h.symm distinct
    · exact absurd h distinct
  · rfl

theorem least_le (a : α) : le least a := .inl rfl

theorem le_greatest (a : α) : le a greatest := .inr rfl

theorem le_join_left [DecidableEq α] (a b : α) : le a (join a b) := by
  unfold join
  split
  · exact le_greatest a
  · rename_i h
    exact .inl (((cases a).resolve_right fun h' => h (.inl h')))

theorem le_join_right [DecidableEq α] (a b : α) : le b (join a b) := by
  unfold join
  split
  · exact le_greatest b
  · rename_i h
    exact .inl (((cases b).resolve_right fun h' => h (.inr h')))

/-- The join is the least point above both. -/
theorem join_le [DecidableEq α] {a b c : α} (ha : le a c) (hb : le b c) : le (join a b) c := by
  unfold join
  split
  · rename_i h
    rcases h with h | h
    · rcases ha with ha | ha
      · exact absurd (h.symm.trans ha) (Ne.symm distinct)
      · exact .inr ha
    · rcases hb with hb | hb
      · exact absurd (h.symm.trans hb) (Ne.symm distinct)
      · exact .inr hb
  · exact least_le c

end Axis

/-- Locality: does the value leave the function that binds it (modes.escaping and modes.not-escaping)? -/
inductive Locality where
  | «local»
  | escapes
  deriving DecidableEq, Repr

/-- Uniqueness: at a write, may another path to the value exist (modes.copy-on-write-types, modes.copies and modes.shared-writes)? -/
inductive Uniqueness where
  | unique
  | shared
  deriving DecidableEq, Repr

/-- Once: may the closure run more than once (modes.once-closures and modes.once-parameters)? -/
inductive Once where
  | once
  | many
  deriving DecidableEq, Repr

/-- Portability: may the value go to another task (modes.fixed-values)? -/
inductive Portability where
  | portable
  | fixed
  deriving DecidableEq, Repr

/-- Contention: may several tasks reach the value at once (modes.contended-values)? -/
inductive Contention where
  | calm
  | contended
  deriving DecidableEq, Repr

instance : Axis Locality := ⟨.local, .escapes, fun a => by cases a <;> simp, by decide⟩
instance : Axis Uniqueness := ⟨.unique, .shared, fun a => by cases a <;> simp, by decide⟩
instance : Axis Once := ⟨.once, .many, fun a => by cases a <;> simp, by decide⟩
instance : Axis Portability := ⟨.portable, .fixed, fun a => by cases a <;> simp, by decide⟩
instance : Axis Contention := ⟨.calm, .contended, fun a => by cases a <;> simp, by decide⟩

/-- The modes of a binding: a `let` or `var` binding, a parameter, or a closure
literal, one point on each axis (modes.bindings-and-axes). The once axis has a point
only for a closure literal or a parameter of function type. -/
structure Modes where
  locality : Locality
  uniqueness : Uniqueness
  once : Option Once
  portability : Portability
  contention : Contention
  deriving DecidableEq, Repr

namespace Modes

/-- The defaults of modes.bindings-and-axes: `local`, `unique`, `many` for a closure, `portable`
and `calm`. -/
def default (closure : Bool) : Modes :=
  ⟨.local, .unique, if closure then some .many else none, .portable, .calm⟩

/-- The words `show` prints for a binding's modes: one for each mode other than
the default (modes.show). A closure literal's default is `many`. -/
def words (m : Modes) : List String :=
  (if m.locality = .escapes then ["escapes"] else []) ++
  (if m.uniqueness = .shared then ["shared"] else []) ++
  (if m.once = some .once then ["once"] else []) ++
  (if m.portability = .fixed then ["fixed"] else []) ++
  (if m.contention = .contended then ["contended"] else [])

/-- A binding at its defaults prints nothing (modes.show). -/
theorem words_default (closure : Bool) : (default closure).words = [] := by
  cases closure <;> rfl

end Modes

/-! ## The thread axes -/

/-- Whether a type is fixed (modes.fixed-values): `View<T>` is (views.fixed), and no
core type is. No other type of the calculus holds a view (views.view-types). -/
def Ty.fixed : Ty → Bool
  | .view _ => true
  | _ => false

/-- Whether a type holds `Shared<T>` (modes.contended-values), which the calculus,
like core, doesn't have. -/
def Ty.contended (_ : Ty) : Bool := false

/-- A binding of type `τ` is `fixed` when its type holds a fixed type, or when
it is a closure literal that captures a binding of a fixed type (modes.fixed-values and modes.mode-crossing). -/
def portabilityOf (τ : Ty) (captured : List Ty) : Portability :=
  if τ.fixed || captured.any Ty.fixed then .fixed else .portable

/-- A binding of type `τ` is `contended` when its type holds `Shared<T>`, or
when it is a closure literal that captures a contended binding (modes.contended-values and modes.mode-crossing). -/
def contentionOf (τ : Ty) (captured : List Ty) : Contention :=
  if τ.contended || captured.any Ty.contended then .contended else .calm

/-- Every binding of the calculus is `calm` (modes.contended-values and modes.mode-crossing). -/
theorem calm (τ : Ty) (captured : List Ty) : contentionOf τ captured = .calm := by
  simp [contentionOf, Ty.contended]

/-- A binding that captures nothing is `fixed` exactly when its type is a view type
(modes.fixed-values and views.fixed). -/
theorem portabilityOf_fixed_iff (τ : Ty) :
    portabilityOf τ [] = .fixed ↔ ∃ σ, τ = .view σ := by
  cases τ <;> simp [portabilityOf, Ty.fixed]

end Stilt
