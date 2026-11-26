import Stilt.Typing.Bounds

/-!
# Uses of generic functions

What a use of a generic function asks of the arguments it gives: of its row arguments, that
they pass on a row variable of the enclosing function only with its pairing, and of its type
arguments, that they meet the parameters' bounds. The typing judgment of `Stilt.Typing`
reads both at `fnRef`.
-/

namespace Stilt

/-- The signature pairs `v` with `E`: some row of its parameter types, at any
depth, or its own row holds both `v` and `raise<E>` (effects.paired-row-variables). The rows
are those of the elaborated signature, so a non-escaping parameter's implicit
variable, which its own row and the function's hold, is paired with `E` when
either names `raise<E>`. -/
def FnDecl.pairs (d : FnDecl) (v : Name) (E : Ty) : Prop :=
  ∃ ρ ∈ paramRows (d.params.map Param.sig) ++ [d.row], v ∈ ρ.vars ∧ ρ.raise = some E

/-- A use of `d` that instantiates its row variables with `s` passes on a row
variable of the enclosing function only with its pairing: where `d` pairs `v`
with `E` and `s` gives `v` a row that holds `r`, written or implicit, the
enclosing scope pairs `r` with the type the use gives `E` (effects.passing-to-paired-variables).

With effects.one-error-type, which leaves each row of the instantiated signature one
`raise` label, this keeps `v` from adding any error type but `E`: a concrete
instantiation is limited by effects.one-error-type, and one that holds `r` is limited by the
pairing of `r`, which every use of the enclosing function checks in turn. -/
def PassesOnPairs (scope : RowScope) (d : FnDecl) (s : RowSubst) : Prop :=
  ∀ v E ρ r, d.pairs v E → s.lookup v = some ρ → r ∈ ρ.vars →
    scope.passOn r (E.substRows s)

/-- `τ` implements the trait `B`, as far as a body whose type parameters `scope` describes
knows: a type parameter through its bounds, which are all the body knows of it; a type
with a head through the program's impl of `B` for that head (traits.unsatisfied-bounds and
traits.implementing-trait); and for `Eq`, `Ord` and `Show`, a type that implements them
through the built-in and structural impls, which the calculus's operations compute
(traits.built-in-impls and traits.structural-impls). The model leaves out the impls of
`Eq`, `Ord` and `Show` that a program writes. -/
def Satisfies (D : Decls) (scope : RowScope) (τ : Ty) (B : Name) : Prop :=
  (∃ p ∈ scope.types, τ = .param p.name ∧ B ∈ p.bounds) ∨
    (PreludeTrait.ofName? B = none ∧ ∃ h, τ.head? = some h ∧ (D.traitImpl? B h).isSome) ∨
    ∃ t, PreludeTrait.ofName? B = some t ∧ D.Implements scope t τ

/-- The type arguments of a use of a function, one for each of its type
parameters: closed, well formed where the use is, and meeting the parameter's
bounds (traits.unsatisfied-bounds). -/
def TypeArgsFit (D : Decls) (scope : RowScope) (ps : List TypeParam) (τs : List Ty) : Prop :=
  Forall₂ (fun p τ => τ.Closed ∧ τ.WellFormed scope ∧ ∀ B ∈ p.bounds, Satisfies D scope τ B) ps τs

end Stilt
