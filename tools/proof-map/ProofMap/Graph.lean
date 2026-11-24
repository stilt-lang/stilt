import Lean

/-!
# The declarations of the model and what each uses

A declaration is the model's when its module is under `Stilt` and it has a source range,
so it was written in a file rather than made by the elaborator (a `match_` or a
`proof_` helper, an equation lemma, a recursor). What a declaration's statement and
proof use is read through the made ones: a proof that calls `foo.match_1` uses what
that helper uses.
-/

open Lean

namespace ProofMap

/-- One written declaration of the model. -/
structure Decl where
  name : Name
  kind : String
  module : Name
  line : Nat
  doc : Option String
  /-- The written declarations its statement uses. -/
  statement : Array Name
  /-- The written declarations its proof or body uses. -/
  body : Array Name
  /-- The axioms it rests on, beyond `propext`, `Classical.choice` and `Quot.sound`. -/
  axioms : Array Name
  deriving Inhabited

/-- The axioms every Lean development may rest on. -/
def standardAxioms : List Name := [``propext, ``Classical.choice, ``Quot.sound]

/-- The module that declares `n`, if an imported one does. -/
def moduleOf (env : Environment) (n : Name) : Option Name :=
  env.getModuleIdxFor? n |>.map fun i => env.header.moduleNames[i.toNat]!

/-- Whether `n` belongs to the model: declared in a module under `Stilt`. -/
def inModel (env : Environment) (n : Name) : Bool :=
  match moduleOf env n with
  | some m => (`Stilt).isPrefixOf m
  | none => false

/-- The kind of a declaration, as the page names it. -/
def kindOf (env : Environment) (ci : ConstantInfo) : String :=
  match ci with
  | .thmInfo _ => "theorem"
  | .defnInfo _ => if Meta.isInstanceCore env ci.name then "instance" else "def"
  | .inductInfo _ => if isStructure env ci.name then "structure" else "inductive"
  | .ctorInfo _ => "constructor"
  | .axiomInfo _ => "axiom"
  | .opaqueInfo _ => "opaque"
  | .recInfo _ => "recursor"
  | .quotInfo _ => "quotient"

/-- The constants an expression names, without repeats. -/
def used (e : Expr) : Array Name := e.getUsedConstants

end ProofMap
