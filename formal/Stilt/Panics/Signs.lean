import Stilt.Panics.Guards

/-!
# Known signs and the facts a binding gives

The rules of acceptance know some integer expressions not to be negative
(facts.known-signs): a non-negative literal, a call of `len()`, a variable the facts around
it know not negative, and a `+` or a `*` of such expressions (`Expr.nonnegIn`). A literal
constant is its literal in the calculus, which the export writes where the constant is read.
A `let` or a `var` whose initial value is known non-negative gives its name that fact, until
code writes the binding (`Expr.bindFacts`). A binding of a variable gives its name the facts
of keys that the variable's value is (facts.keys): the export binds the key of `m[k] = v`,
and of `m[k] += v`, to a temporary before it stores, as it binds an operand, so the key the
store reads is the variable's.
-/

namespace Stilt

/-- Whether an operation gives a length, `len()` of a string, a list, a map or a set, which
is never negative. -/
def Op.givesLen : Op → Bool
  | .len | .list .len | .map .len | .set .len => true
  | _ => false

/-- Whether an integer expression is known non-negative where the facts `G` hold
(facts.known-signs): a non-negative literal, a variable that `G` knows not negative, a call
of `len()`, and a `+` or a `*` of known non-negative expressions, the second known so where
the first has run. -/
def Expr.nonnegIn : List Known → Expr → Bool
  | _, .int a => decide (0 ≤ a)
  | G, .var a => decide (Known.nonneg a ∈ G)
  | G, .op (.arith o _) [a, b] =>
    (o == .add || o == .mul) && a.nonnegIn G && b.nonnegIn (withoutNames G a.writes)
  | _, .op o [_] => o.givesLen
  | _, _ => false

/-- The fact that a key a map has gives the name `x` of a binding of the variable `a`: the
map has `x`'s value too. -/
def Known.alias (a x : Name) : Known → List Known
  | .has m (.var k) => if k = a ∧ m ≠ x then [.has m (.var x)] else []
  | _ => []

/-- The facts that binding `x` to the value of `init` gives the code in its scope, where the
facts `G` held before `init` ran: that `x` isn't negative when `init` is known non-negative
(facts.known-signs), and, when `init` is a variable, that each map that has the variable's
value as a key has `x`'s (facts.keys). -/
def Expr.bindFacts (G : List Known) (x : Name) (init : Expr) : List Known :=
  (if init.nonnegIn G then [.nonneg x] else []) ++
    match init with
    | .var a => G.flatMap (Known.alias a x)
    | _ => []

end Stilt
