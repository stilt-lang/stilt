/-!
# Record bounds

records.record-bounds lets a type parameter carry a record bound, `P: { f: T, .. }`,
which names fields that every record the parameter stands for has, each with
exactly the bound's type. A body reads `p.f` through the bound, and the
caller's type comes back (records.open-parameter-types). This calculus states the fact that rule
rests on: a read checked through the bound stays well typed, at the bound's
field type, once any type that meets the bound replaces the parameter, so
checking the body once covers every record a call gives it.

Its types are `i64`, `bool`, type parameters, named by their indexes, and
records, whose fields have `i64` or `bool`; its terms are variables, by de
Bruijn index, and reads of fields. A record's fields are in any order, as an
anonymous record's are (records.anonymous-types), since a read finds a field by its name.
-/

namespace Stilt.Records

/-- The types a record's field has in the calculus. -/
inductive Base where
  | int : Base
  | bool : Base
  deriving DecidableEq, Repr

/-- A type of the calculus. -/
inductive Ty where
  | base : Base → Ty
  /-- A type parameter, which only its bound is known of. -/
  | param : Nat → Ty
  /-- A record, declared or anonymous, with its fields. -/
  | record : List (String × Base) → Ty
  deriving DecidableEq, Repr

/-- A record bound: the fields it names, with their types. -/
abbrev Bound := List (String × Base)

/-- records.record-bounds: a type meets a record bound when it is a record that has
each field the bound names, with exactly that type. -/
def Meets (t : Ty) (b : Bound) : Prop :=
  ∃ fs, t = .record fs ∧ ∀ f u, b.lookup f = some u → fs.lookup f = some u

/-- `t.inst p s` is `t` with the parameter `p` replaced by `s`, as a call
instantiates it. A record's fields name no parameter. -/
def Ty.inst : Ty → Nat → Ty → Ty
  | .param q, p, s => if q = p then s else .param q
  | t, _, _ => t

/-- A term of the calculus. -/
inductive Tm where
  | var : Nat → Tm
  | field : Tm → String → Tm
  deriving DecidableEq, Repr

/-- The typing judgment, with the record bound `Δ q` of each type parameter
`q`: the types of the variables in scope, innermost first, a term and its
type. A field is read from a record that has it, or through the bound of a
type parameter that names it (records.record-bounds). -/
inductive HasType (Δ : Nat → Bound) : List Ty → Tm → Ty → Prop where
  | var {Γ : List Ty} {n : Nat} {t : Ty} :
      Γ[n]? = some t → HasType Δ Γ (.var n) t
  | field {Γ : List Ty} {e : Tm} {fs : List (String × Base)} {f : String}
      {u : Base} :
      HasType Δ Γ e (.record fs) → fs.lookup f = some u →
        HasType Δ Γ (.field e f) (.base u)
  | bound {Γ : List Ty} {e : Tm} {q : Nat} {f : String} {u : Base} :
      HasType Δ Γ e (.param q) → (Δ q).lookup f = some u →
        HasType Δ Γ (.field e f) (.base u)

/-- `BoundInstance`: a term checked with the parameter `p` has, once a type
that meets `p`'s bound replaces it, the type that the replacement gives, with
the parameter replaced in the context too. A read through the bound has the
bound's field type, which the record has (records.record-bounds). -/
theorem HasType.inst {Δ : Nat → Bound} {Γ : List Ty} {e : Tm} {t : Ty}
    (h : HasType Δ Γ e t) (p : Nat) (s : Ty) (hs : Meets s (Δ p)) :
    HasType Δ (Γ.map (·.inst p s)) e (t.inst p s) := by
  induction h with
  | var hn => exact .var (by simp [List.getElem?_map, hn])
  | field _ hf ih => exact .field ih hf
  | @bound _ q f u _ hf ih =>
      by_cases hq : q = p
      · subst hq
        obtain ⟨fs, rfl, hall⟩ := hs
        simp only [Ty.inst, ite_true] at ih
        exact .field ih (hall f u hf)
      · simp only [Ty.inst, hq, ite_false] at ih
        exact .bound ih hf

/-- `BoundRead`: the read `p.f` of a parameter `p: P`, where `P`'s bound names
`f: u`, is well typed at `u` for every type that meets the bound. -/
theorem bound_read {Δ : Nat → Bound} {p : Nat} {f : String} {u : Base}
    (hf : (Δ p).lookup f = some u) (s : Ty) (hs : Meets s (Δ p)) :
    HasType Δ [s] (.field (.var 0) f) (.base u) := by
  have body : HasType Δ [.param p] (.field (.var 0) f) (.base u) :=
    .bound (.var rfl) hf
  simpa [Ty.inst] using body.inst p s hs

/-! ## Examples: `fn value<B: { v: i64, .. }>(b: B) -> i64 { b.v }` -/

/-- The bound `{ v: i64, .. }` of the parameter 0. -/
def vBound : Nat → Bound := fun _ => [("v", .int)]

/-- `Box<i64>`, declared `{ v: T }`, at its argument. -/
def boxInt : Ty := .record [("v", .int)]

/-- `{ tag: bool, v: i64 }`, an anonymous record with one more field. -/
def tagged : Ty := .record [("tag", .bool), ("v", .int)]

theorem boxInt_meets : Meets boxInt (vBound 0) :=
  ⟨_, rfl, fun _ _ h => h⟩

theorem tagged_meets : Meets tagged (vBound 0) := by
  refine ⟨_, rfl, fun f u h => ?_⟩
  by_cases hv : f = "v"
  · subst hv
    simpa [vBound, List.lookup] using h
  · have hb : (f == "v") = false := by simpa using hv
    simp [vBound, List.lookup, hb] at h

/-- `b.v` has type `i64` at `Box<i64>`, and at the anonymous record. -/
theorem value_at_box : HasType vBound [boxInt] (.field (.var 0) "v") (.base .int) :=
  bound_read (p := 0) rfl boxInt boxInt_meets

theorem value_at_tagged :
    HasType vBound [tagged] (.field (.var 0) "v") (.base .int) :=
  bound_read (p := 0) rfl tagged tagged_meets

end Stilt.Records
