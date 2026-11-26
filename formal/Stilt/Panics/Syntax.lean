import Stilt.Panics.Overflow
import Stilt.Panics.Guards
import Stilt.Places

/-!
# Code without panics

Whether code holds no operation that adds the implicit effect `panic`
(effects.panicking-operations): no index, whether of a place or of a value
(std.lists) but one that tests or a range loop prove in bounds, no operation that `Op.panicFree` leaves out, but `/`, `%`,
`div_euclid` and `rem_euclid` by a divisor that is proved not zero, and no
closure literal whose body holds one (facts.inference), a handler's bodies
among them; a performance and a `with` add nothing of their own
(handlers.implicit-effects-and-capabilities). A divisor is proved when
it is written as an integer literal other than zero, when it is the variable of
a `for` over a range from a positive literal, which is known positive
(facts.known-signs), or when it is a variable `d` that a test guards, with nothing between them writing `d` (facts.divisors):
`G` holds the variables that the tests around the code guard, the code after
an `if` whose then-branch always jumps counting on the negation of its test, and code drops
each of them that it writes, or that a binding hides, before the code after it.
Naming a function, to call it or as a value, adds `panic` unless it is one of the
functions `lim` covers, which are without `panic` wherever they are named
(effects.without-panic): `Decls.PanicCover` says that they are, and a program is
panic-free when every function it declares is covered (`Program.PanicFree`). Where `lim`
rules out `overflow` too, no operation that can overflow is allowed (`Op.overflowFree`), and
no index computed by arithmetic (effects.without-overflow).
-/

namespace Stilt

/-- `/`, `%` and the integer methods, which a divisor written as a literal other
than zero keeps from panicking (effects.panicking-operations). -/
def Op.byDivisor : Op → Bool
  | .arith _ _ | .intMethod _ _ => true
  | _ => false

/-- `/`, `%` and the integer methods can overflow. -/
theorem Op.overflowFree_of_byDivisor {o : Op} (h : o.byDivisor = true) : o.overflowFree = false := by
  cases o <;> first | rfl | (simp [Op.byDivisor] at h)

/-- Whether an expression is a variable, which reads its value with no arithmetic. -/
def Expr.isVar : Expr → Bool
  | .var _ => true
  | _ => false

/-- Whether the operands of an operation end in a divisor written as an integer
literal other than zero, `n / 2`'s. -/
def literalDivisor : List Expr → Bool
  | [_, .int n] => n != 0
  | _ => false

/-- Whether the operands of an operation end in a divisor that a test guards: a
variable of `G` that the operand before it doesn't write. -/
def guardedDivisor (G : List Known) : List Expr → Bool
  | [a, b] => match b.readVar? with
    | some d => decide (Known.nonzero d ∈ G) && decide (d ∉ a.writes)
    | none => false
  | _ => false

/-- Whether the facts `G` give `0 <= j + k` and `j + k < xs.len()`: from `j >= 0`
and `k >= 0`, or `j >= a` with `a + k >= 0`; and from `j < xs.len()` and `k <= 0`, or
`j + c < xs.len()` with `k <= c`. -/
def Known.bounds (G : List Known) (j xs : Name) (k : Int) : Bool :=
  (decide (0 ≤ k) && decide (Known.nonneg j ∈ G) ||
      G.any fun f => match f with
        | .atLeast y a => y == j && decide (0 ≤ a + k)
        | _ => false) &&
    (decide (k ≤ 0) && decide (Known.below j xs ∈ G) ||
      G.any fun f => match f with
        | .belowBy y ys c => y == j && ys == xs && decide (k ≤ c)
        | _ => false)

/-- Whether `xs[i]` reads a list within its bounds: `xs` is a variable and `i` is a
variable `j`, `j + k` or `j - k` with `k` a literal, and the facts around it give
`0 <= i` and `i < xs.len()`: tests, as `j >= 0 && j < xs.len()` gives them
(facts.guards), or a range loop (facts.range-loops). -/
def guardedIndex (G : List Known) (e i : Expr) : Bool :=
  match e.readVar?, i.offset? with
  | some xs, some (j, k) => Known.bounds G j xs k
  | _, _ => false

/-- Whether `m[k]` reads a key the map has: `m` is a variable, `k` a variable or a
literal, and the tests around it give `m.contains(k)` (facts.keys). -/
def guardedKey (G : List Known) : List Expr → Bool
  | [a, k] => match a.readVar?, k.keyTerm? with
    | some m, some kt => decide (Known.has m kt ∈ G)
    | _, _ => false
  | _ => false

/-- Whether a range's start is a literal or a variable, which reads no more than
the frame. -/
def Expr.isLow : Expr → Bool
  | .int _ | .var _ => true
  | _ => false

/-- The facts that the start of a range gives the loop's variable `x`: from a literal
`a`, that it isn't zero, from a positive start, isn't negative, from one that isn't,
and is no less than `a`; from a variable that the facts `G` before the loop know not
negative, that it isn't negative either (facts.known-signs). The model knows signs from
these alone: not from constants, `len()`, `+` and `*` of known signs, accumulators or
bindings known positive, which facts.known-signs gives too. -/
def Expr.lowFacts (G : List Known) (x : Name) : Expr → List Known
  | .int a => (if 0 < a then [.nonzero x] else []) ++ (if 0 ≤ a then [.nonneg x] else []) ++ [.atLeast x a]
  | .var a => if Known.nonneg a ∈ G then [.nonneg x] else []
  | _ => []

/-- The facts that a `for` over a range from a literal or a variable gives its
variable `x` in its body: its start's, and, up to `xs.len() - c`, that it is below
the list's length by more than `c`, when the body doesn't resize `xs`, storing it
whole or passing it `inout` whole, and `x` isn't `xs` (facts.range-loops). -/
def Expr.rangeFacts (G : List Known) : Expr → Name → Expr → List Known
  | .op (.list (.range inclusive)) [lo, hi], x, body =>
    if lo.isLow then
      lo.lowFacts G x ++
        match inclusive, hi.lenLess? with
        | false, some (xs, c) => if xs ≠ x ∧ xs ∉ body.resizes then [.belowBy x xs c] else []
        | _, _ => []
    else []
  | _, _, _ => []

/-- Whether `xs[e] = value` stores within the list's bounds: the place is one index
below its root, `e` is proved an index of the root's list as `guardedIndex` proves
one, and `value`, which runs after `e`, doesn't resize the list (facts.guards and
facts.range-loops). -/
def guardedStore (G : List Known) (p : Place) (value : Expr) : Bool :=
  match p.path with
  | [.index e] => match e.offset? with
    | some (j, k) => Known.bounds G j p.root k && decide (p.root ∉ value.resizes)
    | none => false
  | _ => false

/-- Whether a step of a place is a field, or an index that a variable gives, which reads
its value with no arithmetic. -/
def Projection.byVar : Projection → Bool
  | .field _ => true
  | .index i => i.isVar

/-- Whether an operation on the operands `es` can't panic, but with `overflow`. -/
def Op.panicFreeOn (G : List Known) (o : Op) (es : List Expr) : Bool :=
  o.panicFree || (o.byDivisor && (literalDivisor es || guardedDivisor G es)) ||
    (o == .map .index && guardedKey G es)

section

variable (lim : Limited)

mutual

/-- Whether `e`, where the tests around it guard the variables of `G`, holds no
operation that adds `panic`, its closure literals' bodies included. A
performance adds none of its own, as a call through a stored function value
doesn't, and neither does a `with`: a handler's bodies are closure literals of
the code that writes them (handlers.implicit-effects-and-capabilities). A `when` adds
only `deadlock`, which `without panic` doesn't rule out
(shared.when-on-value-already-held); its names carry no fact. Naming a function, to call
it or as a value, adds `panic` unless `lim` covers it: a function limited by
`without panic` counts as one that can't panic wherever it is named
(effects.without-panic). A call through a function value adds nothing: a closure
literal's body is checked where it is written, a named function where it is named
(facts.calls-through-function-values). Where `lim` rules out `overflow`, an operation that
can overflow is a site too, and so is an index that arithmetic computes
(effects.without-overflow). -/
def Expr.panicFreeIn : List Known → Expr → Bool
  | _, .var _ | _, .move _ | _, .int _ | _, .bool _ | _, .unit | _, .break | _, .continue => true
  | _, .fnRef f _ _ => lim.fn f
  | _, .method t m _ => lim.method t m
  | G, .record _ fields => fieldsPanicFree G fields
  | G, .variant _ _ es => exprsPanicFree G es
  | G, .list _ es => exprsPanicFree G es
  | G, .op o es => o.panicFreeOn G es && (lim.overflows || o.overflowFree) && exprsPanicFree G es
  | G, .view es => es.length == 1 && exprsPanicFree G es
  | G, .field e _ => e.panicFreeIn G
  | G, .index e i => guardedIndex G e i && (lim.overflows || i.isVar)
  | _, .closure _ _ _ body => body.panicFreeIn []
  | G, .call callee args _ =>
    callee.panicFreeIn G && argsPanicFree (withoutNames G callee.writes) args
  | G, .letIn x _ init body =>
    init.panicFreeIn G && body.panicFreeIn (withoutNames (withoutNames G init.writes) [x])
  | G, .varIn x _ init body =>
    init.panicFreeIn G && body.panicFreeIn (withoutNames (withoutNames G init.writes) [x])
  | G, .assign p value =>
    (p.indexFree || guardedStore G p value && (lim.overflows || p.path.all Projection.byVar)) &&
      value.panicFreeIn G
  | G, .seq a b => a.panicFreeIn G && b.panicFreeIn (withoutWrites G a.writes a.resizes ++ a.after)
  | G, .if c _ a b =>
    c.panicFreeIn G && a.panicFreeIn (withoutNames G c.writes ++ c.facts) &&
      b.panicFreeIn (withoutNames G c.writes ++ c.negFacts)
  | G, .match e _ arms => e.panicFreeIn G && armsPanicFree (withoutNames G e.writes) arms
  | G, .for x _ e body =>
    e.panicFreeIn G &&
      body.panicFreeIn (withoutNames (withoutNames (withoutNames G e.writes) body.writes) [x] ++
        e.rangeFacts G x body)
  | G, .raise e => e.panicFreeIn G
  | G, .try e => e.panicFreeIn G
  | G, .tryCatch e _ x handler _ =>
    e.panicFreeIn G && handler.panicFreeIn (withoutNames (withoutNames G e.writes) [x])
  | _, .while c body => c.panicFreeIn [] && body.panicFreeIn c.facts
  | _, .loop body => body.panicFreeIn []
  | G, .return e => e.panicFreeIn G
  | G, .perform _ e => e.panicFreeIn G
  | G, .withH _ _ h b => h.panicFreeIn G && b.panicFreeIn (withoutNames G h.writes)
  | G, .held ns hs body =>
    exprsPanicFree G hs && body.panicFreeIn (withoutNames (withoutNames G (exprsWrites hs)) (ns.map Prod.fst))

/-- Whether no expression of a list adds `panic`, each guarded by what the ones
before it don't write. -/
def exprsPanicFree : List Known → List Expr → Bool
  | _, [] => true
  | G, e :: es => e.panicFreeIn G && exprsPanicFree (withoutNames G e.writes) es

/-- Whether no field of a record literal adds `panic`. -/
def fieldsPanicFree : List Known → List (Name × Expr) → Bool
  | _, [] => true
  | G, (_, e) :: fields => e.panicFreeIn G && fieldsPanicFree (withoutNames G e.writes) fields

/-- Whether no argument of a call adds `panic`: an `inout` argument's place holds
no index. -/
def argsPanicFree : List Known → List Arg → Bool
  | _, [] => true
  | G, .value e :: args => e.panicFreeIn G && argsPanicFree (withoutNames G e.writes) args
  | G, .inout p :: args => p.indexFree && argsPanicFree G args

/-- Whether no arm of a `match` adds `panic`, an arm's binders hiding the facts
about their names. -/
def armsPanicFree : List Known → List Arm → Bool
  | _, [] => true
  | G, ⟨_, binders, body⟩ :: arms =>
    body.panicFreeIn (withoutNames G binders) && armsPanicFree G arms

end

/-- Whether `e` holds no operation that adds `panic`, with no test around it. -/
def Expr.panicFree (e : Expr) : Bool := e.panicFreeIn lim []

end

/-- The functions that `lim` covers hold no operation that adds `panic`, and name only
functions it covers, and each impl's method `m` of a trait `t` is covered when `t.m` is:
code under `without panic` can count on every function it names
(effects.without-panic). -/
structure Decls.PanicCover (D : Decls) (lim : Limited) : Prop where
  fns : ∀ d ∈ D.fns, lim.fn d.name = true → d.body.panicFree lim = true
  methods : ∀ t m h i, lim.method t m = true → D.traitImpl? t h = some i →
    lim.fn (implName t h m) = true

/-- Every body a program declares, and `main`, holds no operation that adds
`panic`: the whole program is limited by `without panic` (effects.without-panic). -/
def Program.PanicFree (p : Program) : Prop :=
  (∀ d ∈ p.decls.fns, d.body.panicFree Limited.all = true) ∧ p.main.panicFree Limited.all = true

theorem Program.PanicFree.cover {p : Program} (hp : p.PanicFree) : p.decls.PanicCover Limited.all :=
  ⟨fun d hd _ => hp.1 d hd, fun _ _ _ _ _ _ => rfl⟩

end Stilt
