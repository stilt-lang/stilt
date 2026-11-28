import Stilt.Syntax.Types

/-!
# Declarations as kinds read them

A program's traits, impls and functions as it writes them, with each type as far as kinds read
it: what heads it and how many arguments are written after its head. The export writes them for
the modules of the program, the standard library's left out, since none of its traits is over
type constructors; the functions themselves run as the instances the export writes for each use,
which name no constructor parameter (`Stilt.Kinds`).
-/

namespace Stilt

/-- A type as a declaration writes it, as far as kinds read it: a named type constructor with the
arguments written after it, none for `i64` or for a constructor named alone, as an impl's type
`Option` is; a type parameter, `Self` among them, with the arguments written after it, none for a
plain one; or another type, a tuple, a function type or an anonymous record, whose parts are
types. A member type `C.Item` is the type parameter that elaboration declares for it. -/
inductive KTy where
  | con (name : Name) (args : List KTy)
  | param (name : Name) (args : List KTy)
  | other (parts : List KTy)
  deriving Repr, Inhabited

mutual

/-- Whether two types as kinds read them are one. -/
def KTy.decEq : (a b : KTy) → Decidable (a = b)
  | .con n as, .con m bs =>
    if h : n = m then
      match KTy.decEqList as bs with
      | isTrue h' => isTrue (h ▸ h' ▸ rfl)
      | isFalse h' => isFalse fun e => by cases e; exact h' rfl
    else isFalse fun e => by cases e; exact h rfl
  | .param n as, .param m bs =>
    if h : n = m then
      match KTy.decEqList as bs with
      | isTrue h' => isTrue (h ▸ h' ▸ rfl)
      | isFalse h' => isFalse fun e => by cases e; exact h' rfl
    else isFalse fun e => by cases e; exact h rfl
  | .other as, .other bs =>
    match KTy.decEqList as bs with
    | isTrue h => isTrue (h ▸ rfl)
    | isFalse h => isFalse fun e => by cases e; exact h rfl
  | .con _ _, .param _ _ | .con _ _, .other _ | .param _ _, .con _ _
  | .param _ _, .other _ | .other _, .con _ _ | .other _, .param _ _ =>
    isFalse fun e => by cases e

/-- Whether two lists of types are one. -/
def KTy.decEqList : (as bs : List KTy) → Decidable (as = bs)
  | [], [] => isTrue rfl
  | a :: as, b :: bs =>
    match KTy.decEq a b, KTy.decEqList as bs with
    | isTrue h, isTrue h' => isTrue (h ▸ h' ▸ rfl)
    | isFalse h, _ => isFalse fun e => h (List.cons.inj e).1
    | _, isFalse h' => isFalse fun e => h' (List.cons.inj e).2
  | [], _ :: _ | _ :: _, [] => isFalse fun e => by cases e

end

instance : DecidableEq KTy := KTy.decEq

/-- The receiver of a function: none, `self` with no type written, or `self: T`, which a
method writes in a trait over type constructors and its impls. -/
inductive KReceiver where
  | none
  | bare
  | typed (τ : KTy)
  deriving DecidableEq, Repr, Inhabited

/-- A function's signature as kinds read it: its own generics, each with the traits of its
bounds and named by its position, so that the members of a trait and of an impl compare
whatever names they give them; its receiver; and its parameters' and its result's types. -/
structure KSig where
  name : Name
  generics : List (Name × List Name)
  receiver : KReceiver
  params : List KTy
  result : KTy
  deriving DecidableEq, Repr, Inhabited

/-- A trait: the number of arguments its members write `Self` with, 0 for a trait over types,
its own parameters, and its members' signatures. -/
structure KTrait where
  name : Name
  arity : Nat
  params : List Name
  members : List KSig
  deriving Repr, Inhabited

/-- An impl: its trait, none for an inherent block, its type as written, its own generics with
their bounds, and its members' signatures, with the defaults of its trait that it leaves out. -/
structure KImpl where
  trait : Option Name
  type : KTy
  generics : List (Name × List Name)
  members : List KSig
  deriving Repr, Inhabited

/-- A use of a function with constructor parameters, as an instance: the function, and the
named constructor each of its constructor parameters takes. -/
structure KUse where
  fn : Name
  ctors : List (Name × Name)
  deriving Repr, Inhabited

/-- A program's declarations as kinds read them: the number of type parameters of each named
constructor they name, its traits, its impls, its functions at the top level, and the uses of
those with constructor parameters. -/
structure Kinds where
  arities : List (Name × Nat) := []
  traits : List KTrait := []
  impls : List KImpl := []
  functions : List KSig := []
  uses : List KUse := []
  deriving Repr, Inhabited

end Stilt
