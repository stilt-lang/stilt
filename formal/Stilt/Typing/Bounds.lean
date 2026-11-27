import Stilt.Generics
import Stilt.Ops

/-!
# The prelude traits behind operations

`==` and `!=` stand behind `Eq`, the ordering operators and sorting behind `Ord`, and
interpolation behind `Show` (traits.operators and traits.required-traits), and the
calculus has them as the operations of the prelude's built-in and structural impls. `Hash`
stands behind map keys with `Eq`, which `Stilt.Maps` checks as key types, and a bound of it is
met through the same impls. So an
operation applies only at a type that implements its trait: one with a built-in impl, one
whose structural impl applies because every component implements the trait, or a type
parameter whose bounds name it (traits.unsatisfied-bounds). Function types and `Shared<T>`
implement none, and maps and sets have no `Ord`.
-/

namespace Stilt

/-- The prelude traits that operations of the calculus stand behind, and `Hash`, which
stands behind map keys. -/
inductive PreludeTrait where
  | eq
  | ord
  | «show»
  | hash
  deriving DecidableEq, Repr

/-- A prelude trait's name. -/
def PreludeTrait.name : PreludeTrait → Name
  | .eq => "Eq"
  | .ord => "Ord"
  | .show => "Show"
  | .hash => "Hash"

/-- The prelude trait that a name names, if it names one. -/
def PreludeTrait.ofName? : Name → Option PreludeTrait
  | "Eq" => some .eq
  | "Ord" => some .ord
  | "Show" => some .show
  | "Hash" => some .hash
  | _ => none

theorem PreludeTrait.ofName?_name : ∀ t : PreludeTrait, ofName? t.name = some t
  | .eq | .ord | .show | .hash => rfl

/-- The names of a prelude trait's functions, as `std.prelude` declares them. -/
def PreludeTrait.fns : PreludeTrait → List Name
  | .eq => ["eq"]
  | .ord => ["compare"]
  | .show => ["show", "show_nested"]
  | .hash => ["hash"]

/-- Whether a type whose head is `h` has the structural impl of `t`: the program writes no
impl of `t` for it, which would replace the structural one (traits.structural-impls), and for
`Hash`, no impl of `Eq` either, since a type whose `Eq` the program writes gets no structural
`Hash` (traits.hash-follows-written-eq). -/
def Decls.structuralAt (D : Decls) (t : PreludeTrait) (h : Head) : Bool :=
  (D.traitImpl? t.name h).isNone && (t != .hash || (D.traitImpl? "Eq" h).isNone)

/-- The trait a comparison stands behind: `Eq` for `==` and `!=`, `Ord` for the others
(traits.operators). -/
def Cmp.trait : Cmp → PreludeTrait
  | .eq | .ne => .eq
  | _ => .ord

/-- What implementing `t` asks of a type at its outermost type, given the types `S` its
components must be. The integer and float types, `bool`, `str`, `()` and `Never` have
built-in impls, but for `Hash` of the float types (traits.built-in-impls and traits.floats);
tuples, lists, records and variant types have structural ones when every component
implements `t`, a record's fields and a variant's payloads at the type's arguments, unless
the program writes an impl of `t` for the type, which replaces the structural one, or for
`Hash` writes one of `Eq` (`Decls.structuralAt`, traits.structural-impls). A map has `Eq` when its key
type implements `Eq` and `Hash` and its value type `Eq`, and `Show` when both implement
`Show`; a set has `Eq` when its element type implements `Eq` and `Hash`, and `Show` when
it implements `Show`; neither has `Ord` (traits.map-equality and std.set-impls), nor, in
the calculus, `Hash`. A type
parameter implements what its bounds name, which is all a body knows of it
(traits.unsatisfied-bounds). Function types implement none (traits.built-in-impls), nor
does `Shared<T>` (shared.std-sync). -/
def Decls.ImplStep (D : Decls) (scope : RowScope) (t : PreludeTrait) (S : Ty → Prop) :
    Ty → Prop
  | .int _ | .bool | .str | .unit | .never => True
  | .float _ => t ≠ .hash
  | .tuple τs => ∀ τ ∈ τs, S τ
  | .list τ => S τ
  | .record R args => D.structuralAt t (.record R) = true ∧
      ∃ r, D.record? R = some r ∧ args.length = r.typeParams.length ∧
        ∀ f ∈ r.fieldsAt args, S f.2
  | .variant T args => D.structuralAt t (.variant T) = true ∧
      ∃ v, D.variant? T = some v ∧ args.length = v.typeParams.length ∧
        ∀ c ∈ v.ctorsAt args, ∀ τ ∈ c.2, S τ
  | .map κ υ => match t with
    | .eq => κ.Key ∧ D.Key κ ∧ S υ
    | .show => S κ ∧ S υ
    | .ord | .hash => False
  | .set κ => match t with
    | .eq => κ.Key ∧ D.Key κ
    | .show => S κ
    | .ord | .hash => False
  | .param p => ∃ q ∈ scope.types, q.name = p ∧ t.name ∈ q.bounds
  | .fn .. | .view _ | .shared _ => False

/-- A type that implements the prelude trait `t`, part by part: some set of types holds
it, and each of them implements `t` at its outermost type with its components in the set.
A recursive type implements `t` when its components do. -/
def Decls.Implements (D : Decls) (scope : RowScope) (t : PreludeTrait) (τ : Ty) : Prop :=
  ∃ S : Ty → Prop, S τ ∧ ∀ σ, S σ → D.ImplStep scope t S σ

/-- The prelude traits an operation needs of the types of its operands: `Eq` or `Ord` of
a comparison's operands, `Show` of an interpolated value, and `Ord` of the keys that
`sorted_by` sorts by (traits.required-traits). Every other operation needs none. -/
def Op.traitsNeeded : Op → List Ty → List (PreludeTrait × Ty)
  | .structural c _, τ :: _ => [(c.trait, τ)]
  | .showValue, τ :: _ => [(.show, τ)]
  | .sortedByKey .., .list κ :: _ => [(.ord, κ)]
  | _, _ => []

/-- The types of an operation's operands implement the traits it needs, where the
operation is: a use whose type lacks one is E0318 (traits.unsatisfied-bounds). -/
def Op.BoundsIn (D : Decls) (scope : RowScope) (o : Op) (τs : List Ty) : Prop :=
  ∀ p ∈ o.traitsNeeded τs, D.Implements scope p.1 p.2

/-- An operation that needs no trait needs no impl. -/
theorem Op.boundsIn_of_nil {D : Decls} {scope : RowScope} {o : Op} {τs : List Ty}
    (h : o.traitsNeeded τs = []) : o.BoundsIn D scope τs :=
  fun _ hp => by rw [h] at hp; exact nomatch hp

section

variable {D : Decls} {s s' : RowScope} {t : PreludeTrait}

theorem Decls.ImplStep.mono {S S' : Ty → Prop} (hS : ∀ σ, S σ → S' σ) :
    ∀ {τ : Ty}, D.ImplStep s t S τ → D.ImplStep s t S' τ
  | .int _, h | .float _, h | .bool, h | .str, h | .unit, h | .never, h => h
  | .tuple _, h => fun τ hτ => hS τ (h τ hτ)
  | .list _, h => hS _ h
  | .record .., ⟨hn, r, hr, hl, hf⟩ => ⟨hn, r, hr, hl, fun f hf' => hS _ (hf f hf')⟩
  | .variant .., ⟨hn, v, hv, hl, hc⟩ =>
    ⟨hn, v, hv, hl, fun c hc' τ hτ => hS _ (hc c hc' τ hτ)⟩
  | .map .., h => by
    cases t
    · exact ⟨h.1, h.2.1, hS _ h.2.2⟩
    · exact h
    · exact ⟨hS _ h.1, hS _ h.2⟩
    · exact h
  | .set _, h => by
    cases t
    · exact h
    · exact h
    · exact hS _ h
    · exact h
  | .param _, h => h

/-- What a body knows of its type parameters, kept in a scope that has them all. -/
theorem Decls.ImplStep.of_types {S : Ty → Prop} (hs : ∀ p ∈ s.types, p ∈ s'.types) :
    ∀ {τ : Ty}, D.ImplStep s t S τ → D.ImplStep s' t S τ
  | .param _, ⟨q, hq, h⟩ => ⟨q, hs q hq, h⟩
  | .int _, h | .float _, h | .bool, h | .str, h | .unit, h | .never, h | .tuple _, h
  | .list _, h | .record .., h | .variant .., h | .map .., h | .set _, h => h

theorem Decls.Implements.of_types (hs : ∀ p ∈ s.types, p ∈ s'.types) {τ : Ty}
    (h : D.Implements s t τ) : D.Implements s' t τ :=
  let ⟨S, hτ, hS⟩ := h
  ⟨S, hτ, fun σ hσ => (hS σ hσ).of_types hs⟩

/-- A type that implements `t` implements it at its outermost type, its components
implementing `t`. -/
theorem Decls.Implements.step {τ : Ty} (h : D.Implements s t τ) :
    D.ImplStep s t (D.Implements s t) τ :=
  let ⟨S, hτ, hS⟩ := h
  (hS τ hτ).mono fun _ hσ => ⟨S, hσ, hS⟩

theorem Op.BoundsIn.of_types (hs : ∀ p ∈ s.types, p ∈ s'.types) {o : Op} {τs : List Ty}
    (h : o.BoundsIn D s τs) : o.BoundsIn D s' τs :=
  fun p hp => (h p hp).of_types hs

end

end Stilt
