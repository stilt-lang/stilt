/-!
# The calculus of trait parameters

traits.trait-parameters and traits.member-types gives a trait parameters that its impl's type fixes (traits.trait-parameters and traits.trait-arguments),
names them through a type as member types such as `C.Item` (traits.member-types), and lets
a trait abstract over a type constructor, whose arity its `Self` gives (traits.constructor-traits, traits.constructor-impls and traits.constructor-parameters). This calculus states the two facts those rules rest on: under
coherence, a member type means one type, and replacing a constructor
parameter by a constructor of its arity keeps every type well kinded.

Its types are named type constructors, type parameters, constructor
parameters among them, an application of one to an argument, and member
types. Application is curried: `F<A, B>` is `app (app F A) B`, and a
constructor applied to some of its arguments is no type, since the language
has no partial application (reference/rationale/11-traits.md). Constructors,
parameters and traits are named by their indexes.
-/

namespace Stilt.Traits

/-- A type of the calculus. -/
inductive Ty where
  /-- A named type constructor, such as `i64`, `List` or `Map`. -/
  | con : Nat → Ty
  /-- A type parameter, which may be a constructor parameter (traits.constructor-parameters). -/
  | param : Nat → Ty
  /-- A constructor applied to one more argument. -/
  | app : Ty → Ty → Ty
  /-- `member t k x` is the member type that the impl of trait `t` for `x`
  gives the trait's parameter `k`, as `C.Item` (traits.member-types). -/
  | member : Nat → Nat → Ty → Ty
  deriving DecidableEq, Repr

/-- The head constructor of a type and its arguments, for a named
constructor applied to arguments. -/
def Ty.spine : Ty → Option (Nat × List Ty)
  | .con c => some (c, [])
  | .app f a => (f.spine).map fun p => (p.1, p.2 ++ [a])
  | .param _ => none
  | .member _ _ _ => none

/-- A type of an impl with its type parameters, the arguments of its head
constructor by position, replaced by `targs`. -/
def Ty.inst (targs : List Ty) : Ty → Ty
  | .con c => .con c
  | .param i => targs.getD i (.param i)
  | .app f a => .app (f.inst targs) (a.inst targs)
  | .member t k x => .member t k (x.inst targs)

/-- `t.subst p s` is `t` with the parameter `p` replaced by `s`, as a call
instantiates a generic (traits.constructor-parameters). -/
def Ty.subst : Ty → Nat → Ty → Ty
  | .con c, _, _ => .con c
  | .param q, p, s => if q = p then s else .param q
  | .app f a, p, s => .app (f.subst p s) (a.subst p s)
  | .member t k x, p, s => .member t k (x.subst p s)

/-- An impl of trait `trait` for the constructor `head` applied to its type
parameters, which gives the trait's parameters `args`, written in terms of
those type parameters (traits.trait-arguments): `impl<T> Collection<T> for List<T>`
is `⟨collection, list, [.param 0]⟩`. -/
structure Impl where
  trait : Nat
  head : Nat
  args : List Ty
  deriving DecidableEq, Repr

end Stilt.Traits
