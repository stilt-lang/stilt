/-!
# Capabilities

The names of the capabilities, which `Limits` lists and `Stilt.Capabilities` infers.
-/

namespace Stilt

/-- The eight capabilities below `io`, in their order: `fs`, `net`, `clock`, `env`, `console`,
`rand`, `spawn` and `exec` (`Stilt.Capabilities`). -/
inductive Cap where
  | fs | net | clock | env | console | rand | spawn | exec
  deriving DecidableEq, Repr

end Stilt
