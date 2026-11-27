import Stilt.Syntax

/-!
# Reading and writing the world

The operations on the world that read or write its output, its standard error or its input,
which type only where the row holds `io` (`HasType.op`).
-/

namespace Stilt

/-- Whether an operation on the world reads or writes its output, its standard error or its
input: `print`, `eprint`, and `std.io`'s writes and reads, natives whose rows hold `io` and
which have the capability `console` (std.io). They are the
calculus's natives that have a capability: it has none of `std.fs`, `std.net`, `std.clock`,
`std.cli`, `std.random` or `std.process`, and `std.task`'s `spawn` is a call through a binding.
`Shared.new` makes a cell, and has neither. -/
def WorldOp.io : WorldOp → Bool
  | .sharedNew _ => false
  | _ => true

/-- Whether an operation reads or writes the world's output, standard error or input: only
the operations on the world that `WorldOp.io` picks. -/
def Op.io : Op → Bool
  | .world k => k.io
  | _ => false

/-- An operation that neither reads nor writes the world's output or input asks nothing of
the row it sits in. -/
theorem Op.noIo {o : Op} {b : Bool} (h : o.io = false) : o.io = true → b = true :=
  fun h' => absurd (h ▸ h') Bool.false_ne_true

end Stilt
