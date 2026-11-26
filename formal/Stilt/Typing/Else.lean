import Stilt.Generics

/-!
# Let-else and the `Option` fallback

What the typing rules `HasType.letElse` and `HasType.orElse` of `Stilt.Typing` ask of the parts
of a let-else and of an `Option` fallback beside the `match` each means: which patterns are
irrefutable, which a let-else's must not be, and the prelude's `Option`, the only type a
fallback takes. `Expr.letElse` and `Expr.orElse` write each form as `Expr.form` keeps it.
-/

namespace Stilt

/-- A pattern is **irrefutable** when its form alone guarantees a match
(patterns.irrefutable-positions): `_`, a binding and `()`; a tuple or record pattern whose parts
are irrefutable; a variant of a type with a single variant, whose payload patterns are
irrefutable; `[..]` and `[..rest]`; and an or-pattern with an irrefutable alternative. Every
other pattern is refutable, even one that matches every value, as `A(x) | B(x)` does for a type
whose only variants are `A` and `B`. The calculus has no arrays, whose list patterns are
irrefutable when their elements are. Of the positions that must hold an irrefutable pattern, it
reads only the one that must not: a let-else's (`HasType.letElse`); E0321 on the patterns of `let`
and `var` without `else`, of `for` heads and of closure parameters is outside it. -/
inductive Pattern.Irrefutable (D : Decls) : Pattern → Prop
  | wild : Pattern.Irrefutable D .wild
  | bind {x : Name} : Pattern.Irrefutable D (.bind x)
  | unit : Pattern.Irrefutable D .unit
  | tuple {ps : List Pattern} : (∀ p ∈ ps, Pattern.Irrefutable D p) →
      Pattern.Irrefutable D (.tuple ps)
  | record {R : Name} {fields : List (Name × Pattern)} :
      (∀ f ∈ fields, Pattern.Irrefutable D f.2) → Pattern.Irrefutable D (.record R fields)
  | variant {T C : Name} {t : VariantDecl} {ps : List Pattern} :
      D.variant? T = some t → t.ctors.length = 1 → (∀ p ∈ ps, Pattern.Irrefutable D p) →
      Pattern.Irrefutable D (.variant T C ps)
  | rest {r : ListRest} : r ≠ .exact → Pattern.Irrefutable D (.list [] r)
  | orLeft {p q : Pattern} : Pattern.Irrefutable D p → Pattern.Irrefutable D (.or p q)
  | orRight {p q : Pattern} : Pattern.Irrefutable D q → Pattern.Irrefutable D (.or p q)

/-- The name the export gives the prelude's `Option`, a generic variant type declared once. -/
def optionName : Name := "std.prelude.Option"

/-- `T` names the prelude's `type Option<T> = | None | Some(T)`, declared with its one type
parameter and its variants in that order. -/
def Decls.IsOption (D : Decls) (T : Name) : Prop :=
  T = optionName ∧ ∃ t p, D.variant? T = some t ∧ t.typeParams = [p] ∧
    t.ctors = [("None", []), ("Some", [.param p])]

/-- `let P = e else x`, followed by the rest of its block, `rest`, as a let-else: the `match`
`match e { P => rest, _ => x }`, where `bs` are the names `P` binds and `τ` the type of the rest
(patterns.let-else). A `var` let-else's rest starts by binding each name as a `var` of the value
`P` bound to it (patterns.var-bindings). -/
def Expr.letElse (p : Pattern) (bs : List Name) (e : Expr) (τ : Ty) (rest x : Expr) : Expr :=
  .form .letElse (.match e τ [⟨p, bs, rest⟩, ⟨.wild, [], x⟩])

/-- `e₁ else e₂` at the type `τ`, where `T` names `Option`: the `match`
`match e₁ { Some(v) => v, _ => e₂ }` for a name `v` of its own (expressions.option-fallback). -/
def Expr.orElse (T : Name) (τ : Ty) (v : Name) (e₁ e₂ : Expr) : Expr :=
  .form .orElse (.match e₁ τ [⟨.variant T "Some" [.bind v], [v], .var v⟩, ⟨.wild, [], e₂⟩])

end Stilt
