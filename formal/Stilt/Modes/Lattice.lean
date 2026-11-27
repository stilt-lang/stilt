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
point combine. A binding reuses its storage at a last use when it is `local` and `unique`,
and a closure literal gives its captures up at its call when it is `once`: the least points
of their axes (`Modes.reuses`, `Modes.runsOnce`), which `Program.markModes` reads, and so
the soundness theorem.

The thread axes read a binding's type and a closure literal's captures
(`Stilt.Modes.Threads`). No reuse reads either axis.
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

/-- Portability: may the value go to another task (modes.bindings-and-axes)? -/
inductive Portability where
  | portable
  | fixed
  deriving DecidableEq, Repr

/-- Contention: may several tasks reach the value at once (modes.bindings-and-axes)? -/
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

/-- Whether a binding at these modes may give its storage up at a last use: it is `local`
and `unique`, the least points of locality and uniqueness (modes.bindings-and-axes). Its
value leaves no function, and no write shares it. -/
def reuses (m : Modes) : Bool := m.locality == Axis.least && m.uniqueness == Axis.least

/-- Whether a closure literal at these modes is `once`, the least point of the once axis
(modes.bindings-and-axes), and so may give its captures up at its call (modes.once-parameters). -/
def runsOnce (m : Modes) : Bool := m.once == some Axis.least

end Modes

end Stilt
