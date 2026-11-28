import Stilt.Generics.Commute

/-!
# Trait constants

A read of a trait's constant at a type, `T.NAME` or `Type.NAME`, as `Expr.form` keeps it: the
expression of the value that the program declares for that constant at that type, a constant of
the program (`ConstDecl`) named by the trait, the type's head and the constant's name, whose
value is the impl's constant, or the trait's default, at the type (`TaskForm.traitConst`).
-/

namespace Stilt

/-- `m` is the value of the constant `c`, as the program declares it, or as an instance of a
generic body leaves it, with its types replaced: a constant's value is checked with no type
parameter in scope (`Decls.ConstsTyped`), so an instance changes nothing of it. -/
inductive ConstRead (c : ConstDecl) : Expr → Prop
  | value : ConstRead c c.value
  | inst {m : Expr} (s : TySubst) : ConstRead c m → ConstRead c (m.substTys s)

/-- A read of a trait's constant, the constant that the program declares under `name` for it at
the read's type, and the expression of its value. -/
def Expr.traitConstOf (name : Name) (value : Expr) : Expr := .form (.traitConst name) value

end Stilt
