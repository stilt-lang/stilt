import Stilt.Operators

/-!
# Types

The types of the core calculus, its effect rows, and the operations of
effects; and equality of types, which the store of cells of `Stilt.World`
decides to find a cell by its type.
-/

namespace Stilt

/-- The name of a variable, a field, a variant, a type, a function or a row
variable. -/
abbrev Name := String

/-- A parameter mode (modes.kinds-of-access). A parameter written without a mode is a `let`
parameter (declarations.parameters). -/
inductive Mode where
  /-- An independent copy, which the callee can't modify (values.independent-copies and values.passing-values; modes.what-can-be-modified). Passing it never changes the caller's variable. -/
  | «let»
  /-- Access to the caller's place, which keeps every change (values.inout-arguments). -/
  | inout
  deriving DecidableEq, Repr

/-- The integer types (numbers.numeric-types). -/
inductive IntTy where
  | i8 | i16 | i32 | i64 | u8 | u16 | u32 | u64
  deriving DecidableEq, Repr

/-- The float types (numbers.numeric-types). -/
inductive FloatTy where
  | f32 | f64
  deriving DecidableEq, Repr

mutual

/-- Types (declarations.records and declarations.variant-types). Records and variant types are nominal (declarations.records and declarations.variant-types)
and are named by their declarations. -/
inductive Ty where
  /-- An integer type (numbers.numeric-types). -/
  | int (k : IntTy)
  /-- A float type (numbers.numeric-types). -/
  | float (k : FloatTy)
  | bool
  /-- `str`, a string of Unicode scalar values (std.str). -/
  | str
  /-- `()`, whose only value is `()` (declarations.tuples-and-unit). -/
  | unit
  /-- `Never`, which has no values and converts to any type (declarations.never). -/
  | never
  /-- A record type, with its type arguments, one for each of its declaration's type
  parameters (declarations.type-parameters and declarations.type-arguments). -/
  | record (name : Name) (args : List Ty)
  /-- A variant type, with its type arguments (declarations.type-parameters and
  declarations.type-arguments). -/
  | variant (name : Name) (args : List Ty)
  | list (elem : Ty)
  /-- `(A, B, …)`, a tuple type of one element or more; `()` is the unit type
  (declarations.tuples-and-unit). -/
  | tuple (elems : List Ty)
  /-- `Map<K, V>`, whose entries keep insertion order (std.maps). -/
  | map (key value : Ty)
  /-- `Set<T>`, the prelude's record of a `Map<T, ()>` (std.sets). -/
  | set (elem : Ty)
  /-- A type parameter of the function the type is written in
  (declarations.function-declarations), or `Self` in a trait's signatures
  (traits.declaring-trait). -/
  | param (name : Name)
  /-- `fn(m₁ A₁, …) -> R / row`. A parameter's mode is part of the type
  (declarations.function-types). -/
  | fn (params : List (Mode × Ty)) (result : Ty) (row : Row)
  /-- `View<T>`, a window into a part of a value of the viewable type `T`, its
  source (views.what-view-is). -/
  | view (viewed : Ty)
  /-- `Shared<T>`, a handle to a value that tasks share (shared.std-sync). -/
  | shared (elem : Ty)

/-- An effect row (effects.rows). Its elements are unordered, `io` appears
at most once, and a row holds at most one `raise<E>` (effects.one-error-type and
effects.repeated-elements). A row written in
a signature holds at most one row variable, but a function's own row and the
rows a body forms may hold several, since the implicit variables of
non-escaping parameters are never written (effects.row-variables and effects.non-escaping-parameters). So a flag, an
option and lists represent every row, the lists read as sets. -/
structure Row where
  /-- Whether the row holds the label `io`. -/
  io : Bool
  /-- The error type of its `raise<E>` label, if it has one. -/
  raise : Option Ty
  /-- Its row variables, written or implicit. -/
  vars : List Name
  /-- The declared effects it holds (handlers.effects-in-rows). -/
  effects : List Name
  /-- In the body of an operation of a handler that takes control, the type of
  the value `resume` takes and of the value it gives (handlers.resuming). -/
  resume : Option (Ty × Ty)

end

/-- An operation of an effect, by the effect's name and its own
(handlers.declaring-effect). -/
structure Operation where
  effect : Name
  name : Name
  deriving DecidableEq, Repr

/-- The operation that `resume(v)` performs in the body of an operation of a
handler that takes control (handlers.resuming). No effect has its name. -/
def Operation.resume : Operation := ⟨"resume", "resume"⟩

/-- `i64`, the type of lengths, indexes and counts (numbers.lengths-are-i64). -/
@[match_pattern] abbrev Ty.i64 : Ty := .int .i64

/-! ## Equality of types -/

mutual

/-- Whether two types are the same type. -/
def Ty.beq : Ty → Ty → Bool
  | .int k, .int k' => k == k'
  | .float k, .float k' => k == k'
  | .bool, .bool | .str, .str | .unit, .unit | .never, .never => true
  | .param a, .param b => a == b
  | .record a as, .record b bs | .variant a as, .variant b bs => a == b && Ty.beqs as bs
  | .list a, .list b | .set a, .set b | .view a, .view b | .shared a, .shared b => Ty.beq a b
  | .tuple as, .tuple bs => Ty.beqs as bs
  | .map a b, .map c d => Ty.beq a c && Ty.beq b d
  | .fn ps r ρ, .fn qs s σ => Ty.beqParams ps qs && Ty.beq r s && Row.beq ρ σ
  | _, _ => false

/-- Whether two lists of types are the same, position by position. -/
def Ty.beqs : List Ty → List Ty → Bool
  | [], [] => true
  | a :: as, b :: bs => Ty.beq a b && Ty.beqs as bs
  | _, _ => false

/-- Whether two lists of parameter types are the same, modes included. -/
def Ty.beqParams : List (Mode × Ty) → List (Mode × Ty) → Bool
  | [], [] => true
  | (m, a) :: ps, (n, b) :: qs => m == n && Ty.beq a b && Ty.beqParams ps qs
  | _, _ => false

/-- Whether two rows are the same, written the same way. -/
def Row.beq : Row → Row → Bool
  | ⟨i, r, vs, es, re⟩, ⟨i', r', vs', es', re'⟩ =>
    i == i' && Ty.beqRaise r r' && vs == vs' && es == es' && Ty.beqResume re re'

/-- Whether two optional error types are the same. -/
def Ty.beqRaise : Option Ty → Option Ty → Bool
  | none, none => true
  | some a, some b => Ty.beq a b
  | _, _ => false

/-- Whether two optional pairs of types are the same. -/
def Ty.beqResume : Option (Ty × Ty) → Option (Ty × Ty) → Bool
  | none, none => true
  | some (a, b), some (c, d) => Ty.beq a c && Ty.beq b d
  | _, _ => false

end

mutual

theorem Ty.eq_of_beq : ∀ (a : Ty) {b : Ty}, Ty.beq a b = true → a = b
  | .int _, b, h | .float _, b, h | .bool, b, h | .str, b, h | .unit, b, h | .never, b, h
  | .param _, b, h => by cases b <;> simp_all [Ty.beq]
  | .record _ as, b, h | .variant _ as, b, h => by
    cases b <;> simp only [Ty.beq, Bool.false_eq_true, Bool.and_eq_true, beq_iff_eq] at h
    rw [h.1, Ty.eq_of_beqs as h.2]
  | .list a, b, h | .set a, b, h | .view a, b, h | .shared a, b, h => by
    cases b <;> simp only [Ty.beq, Bool.false_eq_true] at h <;> rw [Ty.eq_of_beq a h]
  | .tuple as, b, h => by
    cases b <;> simp only [Ty.beq, Bool.false_eq_true] at h; rw [Ty.eq_of_beqs as h]
  | .map a c, b, h => by
    cases b <;> simp only [Ty.beq, Bool.false_eq_true, Bool.and_eq_true] at h
    rw [Ty.eq_of_beq a h.1, Ty.eq_of_beq c h.2]
  | .fn ps r ρ, b, h => by
    cases b <;> simp only [Ty.beq, Bool.false_eq_true, Bool.and_eq_true] at h
    rw [Ty.eq_of_beqParams ps h.1.1, Ty.eq_of_beq r h.1.2, Row.eq_of_beq ρ h.2]

theorem Ty.eq_of_beqs : ∀ (as : List Ty) {bs : List Ty}, Ty.beqs as bs = true → as = bs
  | [], bs, h => by cases bs <;> simp_all [Ty.beqs]
  | a :: as, bs, h => by
    cases bs <;> simp only [Ty.beqs, Bool.false_eq_true, Bool.and_eq_true] at h
    rw [Ty.eq_of_beq a h.1, Ty.eq_of_beqs as h.2]

theorem Ty.eq_of_beqParams :
    ∀ (ps : List (Mode × Ty)) {qs : List (Mode × Ty)}, Ty.beqParams ps qs = true → ps = qs
  | [], qs, h => by cases qs <;> simp_all [Ty.beqParams]
  | (m, a) :: ps, qs, h => by
    rcases qs with _ | ⟨⟨n, b⟩, qs⟩ <;>
      simp only [Ty.beqParams, Bool.false_eq_true, Bool.and_eq_true, beq_iff_eq] at h
    rw [h.1.1, Ty.eq_of_beq a h.1.2, Ty.eq_of_beqParams ps h.2]

theorem Row.eq_of_beq : ∀ (ρ : Row) {σ : Row}, Row.beq ρ σ = true → ρ = σ
  | ⟨i, r, vs, es, re⟩, ⟨i', r', vs', es', re'⟩, h => by
    simp only [Row.beq, Bool.and_eq_true, beq_iff_eq] at h
    obtain ⟨⟨⟨⟨rfl, hr⟩, rfl⟩, rfl⟩, hre⟩ := h
    rw [Ty.eq_of_beqRaise r hr, Ty.eq_of_beqResume re hre]

theorem Ty.eq_of_beqRaise : ∀ (r : Option Ty) {r' : Option Ty}, Ty.beqRaise r r' = true → r = r'
  | none, r', h => by cases r' <;> simp_all [Ty.beqRaise]
  | some a, r', h => by
    cases r' <;> simp only [Ty.beqRaise, Bool.false_eq_true] at h; rw [Ty.eq_of_beq a h]

theorem Ty.eq_of_beqResume :
    ∀ (r : Option (Ty × Ty)) {r' : Option (Ty × Ty)}, Ty.beqResume r r' = true → r = r'
  | none, r', h => by cases r' <;> simp_all [Ty.beqResume]
  | some (a, b), r', h => by
    rcases r' with _ | ⟨c, d⟩ <;> simp only [Ty.beqResume, Bool.false_eq_true, Bool.and_eq_true] at h
    rw [Ty.eq_of_beq a h.1, Ty.eq_of_beq b h.2]

end

mutual

theorem Ty.beq_refl : ∀ a : Ty, Ty.beq a a = true
  | .int _ | .float _ | .bool | .str | .unit | .never | .param _ => by
    simp [Ty.beq]
  | .record _ as | .variant _ as => by simp [Ty.beq, Ty.beqs_refl as]
  | .list a | .set a | .view a | .shared a => by simp [Ty.beq, Ty.beq_refl a]
  | .tuple as => by simp [Ty.beq, Ty.beqs_refl as]
  | .map a b => by simp [Ty.beq, Ty.beq_refl a, Ty.beq_refl b]
  | .fn ps r ρ => by simp [Ty.beq, Ty.beqParams_refl ps, Ty.beq_refl r, Row.beq_refl ρ]

theorem Ty.beqs_refl : ∀ as : List Ty, Ty.beqs as as = true
  | [] => by simp [Ty.beqs]
  | a :: as => by simp [Ty.beqs, Ty.beq_refl a, Ty.beqs_refl as]

theorem Ty.beqParams_refl : ∀ ps : List (Mode × Ty), Ty.beqParams ps ps = true
  | [] => by simp [Ty.beqParams]
  | (_, a) :: ps => by simp [Ty.beqParams, Ty.beq_refl a, Ty.beqParams_refl ps]

theorem Row.beq_refl : ∀ ρ : Row, Row.beq ρ ρ = true
  | ⟨_, r, _, _, re⟩ => by simp [Row.beq, Ty.beqRaise_refl r, Ty.beqResume_refl re]

theorem Ty.beqRaise_refl : ∀ r : Option Ty, Ty.beqRaise r r = true
  | none => by simp [Ty.beqRaise]
  | some a => by simp [Ty.beqRaise, Ty.beq_refl a]

theorem Ty.beqResume_refl : ∀ r : Option (Ty × Ty), Ty.beqResume r r = true
  | none => by simp [Ty.beqResume]
  | some (a, b) => by simp [Ty.beqResume, Ty.beq_refl a, Ty.beq_refl b]

end

instance : DecidableEq Ty := fun a b =>
  if h : Ty.beq a b then isTrue (Ty.eq_of_beq a h)
  else isFalse fun e => h (e ▸ Ty.beq_refl a)

end Stilt
