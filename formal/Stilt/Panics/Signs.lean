import Stilt.Panics.Guards

/-!
# Known signs and the facts a binding gives

The rules of acceptance know some integer expressions not to be negative
(facts.known-signs): a non-negative literal, a call of `len()`, a variable the facts around
it know not negative, and a `+` or a `*` of such expressions (`Expr.nonnegIn`). A literal
constant is its literal in the calculus, which the export writes where the constant is read.
A `let` or a `var` whose initial value is known non-negative gives its name that fact, and one
whose initial value is an integer literal other than zero, that its name isn't zero, until
code writes the binding (`Expr.bindFacts`). A binding of a variable gives its name the facts
the variable has (`Known.alias`): its sign, its bounds against a list's length, and the keys
that its value is (facts.keys). The export binds the key of `m[k] = v`, and the index and the
operand of a compound assignment, `xs[i] += v` and `x /= 2`, to temporaries before it stores
(`Expr.Compound`), so the index, the divisor and the key the store reads are those the
temporaries have.
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

/-- The fact about the variable `a` that it gives the name `x` of a binding of `a`, which holds
`a`'s value: a map that has `a`'s value as a key has `x`'s, and `x` has `a`'s sign and its bounds
against a list's length, when the binding doesn't hide the map or the list. -/
def Known.alias (a x : Name) : Known → List Known
  | .has m (.var k) => if k = a ∧ m ≠ x then [.has m (.var x)] else []
  | .nonzero y => if y = a then [.nonzero x] else []
  | .nonneg y => if y = a then [.nonneg x] else []
  | .atLeast y c => if y = a then [.atLeast x c] else []
  | .below y xs => if y = a ∧ xs ≠ x then [.below x xs] else []
  | .belowBy y xs c => if y = a ∧ xs ≠ x then [.belowBy x xs c] else []
  | _ => []

/-- The facts that binding `x` to the value of `init` gives the code in its scope, where the
facts `G` held before `init` ran: that `x` isn't negative when `init` is known non-negative
(facts.known-signs), that it isn't zero when `init` is an integer literal other than zero, and,
when `init` is a variable, the variable's facts (`Known.alias`, facts.keys). -/
def Expr.bindFacts (G : List Known) (x : Name) (init : Expr) : List Known :=
  (if init.nonnegIn G then [.nonneg x] else []) ++
    match init with
    | .var a => G.flatMap (Known.alias a x)
    | .int k => if k ≠ 0 then [.nonzero x] else []
    | _ => []

end Stilt
