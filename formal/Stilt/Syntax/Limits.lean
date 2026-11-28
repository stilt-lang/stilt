import Stilt.Syntax.Caps

/-!
# Limits

The limits of a `without` clause, as declarations carry them.
-/

namespace Stilt

/-- The limits of a `without` clause that the calculus reads, `panic`, `overflow`, `div`,
`alloc` and `copy`, each a promise that the code it covers holds no site of the fact, and the
capabilities it names (`Stilt.Capabilities`): those a function's own clause names, joined with
those of its module's header, which cover the bodies of the module's functions (facts.without).
The other limits, `locks` and `unsafe`, name facts that the calculus doesn't have.

`panic`, `overflow`, `alloc`, `div` and `copy` are the implicit effects (facts.implicit-effects):
facts the checks infer from bodies, written in no signature and no part of a function's type,
since a `Row` has no element for them: no row writes `panic` or `alloc` (effects.other-effects,
whose tiers are outside the calculus). E0501, at `panic` or `alloc` written in a row, and the
reading of `overflow`, `div` and `copy` there as row variables, are the export's. -/
structure Limits where
  panic : Bool := false
  overflow : Bool := false
  div : Bool := false
  alloc : Bool := false
  copy : Bool := false
  caps : List Cap := []
  deriving DecidableEq, Repr, Inhabited

end Stilt
