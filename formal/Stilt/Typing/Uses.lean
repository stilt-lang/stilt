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
with a head through the program's impl of `B` for that head, whose parameters' bounds the
type's arguments meet (traits.unsatisfied-bounds and traits.implementing-trait); and for `Eq`, `Ord`, `Show` and `Hash`, a type that implements them
through the built-in and structural impls, which the calculus's operations compute
(traits.built-in-impls and traits.structural-impls). A bound of a prelude trait is met only
through those: an impl of one of them that the program writes is reached through
`Trait.m` (`MethodAt`), and no type parameter stands for its type. -/
inductive Satisfies (D : Decls) (scope : RowScope) : Ty → Name → Prop
  | param {p : TypeParam} {B : Name} :
      p ∈ scope.types → B ∈ p.bounds → Satisfies D scope (.param p.name) B
  | impl {τ : Ty} {B : Name} {h : Head} {i : TraitImpl} :
      PreludeTrait.ofName? B = none → τ.head? = some h → D.traitImpl? B h = some i →
      i.typeParams.length = τ.args.length → (∀ a ∈ τ.args, a.ViewsViewable) →
      (∀ pa ∈ i.typeParams.zip τ.args, ∀ B' ∈ pa.1.bounds, Satisfies D scope pa.2 B') →
      Satisfies D scope τ B
  | prelude {τ : Ty} {B : Name} {t : PreludeTrait} :
      PreludeTrait.ofName? B = some t → D.Implements scope t τ → Satisfies D scope τ B

/-- What a body knows of its type parameters, kept in a scope that has them all. -/
theorem Satisfies.of_types {D : Decls} {s s' : RowScope} (hs : ∀ p ∈ s.types, p ∈ s'.types)
    {τ : Ty} {B : Name} (h : Satisfies D s τ B) : Satisfies D s' τ B := by
  induction h with
  | param hp hB => exact .param (hs _ hp) hB
  | impl hn hh hi hl hv _ ih => exact .impl hn hh hi hl hv ih
  | prelude ht hi => exact .prelude ht (hi.of_types hs)

/-- The impl of a trait for a type's head applies to the type: one argument for each of the
impl's parameters, each meeting its bounds (traits.implementing-trait), and each with views
of viewable types alone, as a type argument has. -/
def ImplApplies (D : Decls) (scope : RowScope) (i : TraitImpl) (τ : Ty) : Prop :=
  i.typeParams.length = τ.args.length ∧ (∀ a ∈ τ.args, a.ViewsViewable) ∧
    ∀ pa ∈ i.typeParams.zip τ.args, ∀ B ∈ pa.1.bounds, Satisfies D scope pa.2 B

/-- The arguments `args` that `τ` gives the parameters of the trait `B`, as far as a body
whose type parameters `scope` describes knows: a type parameter through a bound of `B` that
writes them, and a type with a head through the program's impl of `B` for it, whose type fixes
them, at the type's arguments (traits.trait-arguments and traits.bound-arguments). A type
meets a bound that writes arguments when it gives the trait those. -/
def TraitArgs (D : Decls) (scope : RowScope) (τ : Ty) (B : Name) (args : List Ty) : Prop :=
  (∃ p ∈ scope.types, τ = .param p.name ∧ B ∈ p.bounds ∧ p.argsOf B = some args) ∨
    ∃ h i, τ.head? = some h ∧ D.traitImpl? B h = some i ∧ i.typeParams.length = τ.args.length ∧
      i.args.map (Ty.substTys (i.typeArgs τ.args)) = args

/-- `Trait.m` at `τ` names a function that the evaluator finds (traits.qualified-calls), at
the arguments `args` of the trait's parameters: the function of a trait other than `Eq`, `Ord`,
`Show` and `Hash` at a type parameter bounded by the trait, whose bound gives the arguments,
none for a trait without parameters, or the function of the impl that the program writes
for `τ`'s head, which applies to `τ`, at the arguments the impl gives, an impl of a prelude
trait among them, which replaces the structural one (traits.structural-impls). So `a == b`
at a type whose `Eq` the program writes is `Eq.eq(a, b)`, a call of the impl's method, and
`a < b` tests the `Ordering` that `Ord.compare(a, b)` gives (traits.operators). The built-in
and structural impls of the prelude traits are the calculus's operations, which no `Trait.m`
names. -/
def MethodAt (D : Decls) (scope : RowScope) (τ : Ty) (Tr : Name) (args : List Ty) : Prop :=
  (PreludeTrait.ofName? Tr = none ∧ ∃ p ∈ scope.types, τ = .param p.name ∧ Tr ∈ p.bounds ∧
      (p.argsOf Tr = some args ∨ args = [] ∧ ∃ t, D.trait? Tr = some t ∧ t.params = [])) ∨
    ∃ h i, τ.head? = some h ∧ D.traitImpl? Tr h = some i ∧ ImplApplies D scope i τ ∧
      i.args.map (Ty.substTys (i.typeArgs τ.args)) = args

/-- A relation that pairs two lists pairs them under a weaker one. -/
theorem Forall₂.imp {α β : Type} {R R' : α → β → Prop} (h : ∀ {x y}, R x y → R' x y) :
    ∀ {xs : List α} {ys : List β}, Forall₂ R xs ys → Forall₂ R' xs ys
  | _, _, .nil => .nil
  | _, _, .cons hxy hs => .cons (h hxy) (Forall₂.imp h hs)

/-- A relation that pairs two lists pairs the first with the second's images under a relation
that pairs each element with its image. -/
theorem Forall₂.imp_map {α β γ : Type} {R : α → β → Prop} {R' : α → γ → Prop} {f : β → γ}
    (h : ∀ x y, R x y → R' x (f y)) :
    ∀ {xs : List α} {ys : List β}, Forall₂ R xs ys → Forall₂ R' xs (ys.map f)
  | _, _, .nil => .nil
  | _, _, .cons hxy hs => .cons (h _ _ hxy) (Forall₂.imp_map h hs)

theorem Forall₂.length_eq {α β : Type} {R : α → β → Prop} :
    ∀ {xs : List α} {ys : List β}, Forall₂ R xs ys → xs.length = ys.length
  | _, _, .nil => rfl
  | _, _, .cons _ h => by simp [Forall₂.length_eq h]

/-- The type arguments of a use of a function, one for each of its type
parameters: closed, well formed where the use is, and meeting the parameter's
bounds (traits.unsatisfied-bounds), a bound that writes its trait's arguments at the use's
type arguments, which its arguments may name (traits.bound-arguments). -/
def TypeArgsFit (D : Decls) (scope : RowScope) (ps : List TypeParam) (τs : List Ty) : Prop :=
  Forall₂ (fun p τ => τ.Closed ∧ τ.WellFormed scope ∧ ∀ B ∈ p.bounds, Satisfies D scope τ B ∧
      ∀ args, p.argsOf B = some args → (∀ a ∈ args, ∀ T ∈ a.params, T ∈ ps.map TypeParam.name) ∧
        TraitArgs D scope τ B (args.map (Ty.substTys ((ps.map TypeParam.name).zip τs)))) ps τs

end Stilt
