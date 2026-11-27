import Stilt.Ends.Theorem

/-!
# Code that ends

Which code `without div` accepts (facts.div): `quad(n)`, which calls `double`
twice, inside a `for` loop over a list. The check accepts it, and it ends at
fuel 10, whatever the number of turns, and not at 9. It rejects `f(n) = f(n)`,
recursion that doesn't descend, which runs out of the fuel it is given. It accepts a
self-call on a strict part of a parameter (facts.descending-self-calls): `sum` of a tree,
through a pattern, through a binding that holds a part and through a field of a record, and
rejects one on the parameter whole, on a tree it builds, on a part it writes and on an element
of a list. It accepts self-calls that shrink (facts.shrinking-recursion), `count(n - 1)` in the
`else` branch of `n <= 0` and `go(i + 1, n)` under `i < n`, and rejects one under `n == 0`, one
that steps away from its bound, and one that changes its bound. It accepts a `while` that
counts toward its
bound (facts.counting-loops), which needs a fuel more for each turn, and
rejects one whose step is missing, conditional, after a `continue`, zero or
away from the bound, or whose body writes what the bound reads.
-/

namespace Stilt.Examples.Ends

/-- `a + b` on `i64`s. -/
private def add (a b : Expr) : Expr := .op (.arith .add .i64) [a, b]

private def fn (name : Name) (body : Expr) : FnDecl :=
  ⟨name, [], [], [⟨.let, "n", .i64, none⟩], .i64, Row.pure, body, {}⟩

private def call (f : Name) (e : Expr) (result : Ty :=
  .i64) : Expr := .call (.fnRef f [] []) [.value e] result

/-- `fn double(n: i64) -> i64 { n + n }` and `fn quad(n: i64) -> i64 { double(double(n)) }`. -/
private def decls : Decls :=
  ⟨[], [], [fn "double" (add (.var "n") (.var "n")), fn "quad" (call "double" (call "double" (.var "n")))],
    [], [], [], [], []⟩

/-- `var s = 0; for x in [1, 2, 3] { s = s + quad(x) }; raise s`. -/
private def summed : Program :=
  ⟨decls, .varIn "s" .i64 (.int 0) (.seq
    (.for "x" .i64 (.list .i64 [.int 1, .int 2, .int 3])
      (.assign ⟨"s", []⟩ (add (.var "s") (call "quad" (.var "x")))))
    (.raise (.var "s"))), ⟨false, some .i64, [], [], none⟩, {}⟩

example : summed.divFree = true := rfl
example : summed.DivFree := Program.divFree_spec rfl
example : (summed.runCopy 10).observe = .raised (.int 24) := rfl
example : (summed.runCopy 9).observe = .outOfFuel := rfl

/-- `fn f(n: i64) -> i64 { f(n) }`. -/
private def forever : Program :=
  ⟨⟨[], [], [fn "f" (call "f" (.var "n"))], [], [], [], [], []⟩, call "f" (.int 0), ⟨false, some .i64, [], [], none⟩, {}⟩

example : forever.divFree = false := rfl
example : (forever.runCopy 12).observe = .outOfFuel := rfl

example : Expr.divFree Limited.all (fun _ => 0) none [] (.while (.bool true) .unit) = false := rfl
/-- `when c { x }` adds no `div` (shared.when). -/
example : Expr.divFree Limited.all (fun _ => 0) none [] (.held [("x", .i64)] [.var "c"] (.var "x")) = true :=
  rfl

/-! ## Descending recursion -/

/-- `type Tree = | Leaf | Node(Tree, i64, Tree)`. -/
private def tree : VariantDecl := ⟨"Tree", [("Leaf", []), ("Node", [.variant "Tree" [], .i64, .variant "Tree" []])], []⟩

private def leaf : Expr := .variant "Tree" [] "Leaf" []
private def node (l v r : Expr) : Expr := .variant "Tree" [] "Node" [l, v, r]

private def treeFn (name : Name) (body : Expr) : FnDecl :=
  ⟨name, [], [], [⟨.let, "t", .variant "Tree" [], none⟩], .i64, Row.pure, body, {}⟩

/-- `match t { Leaf => 0, Node(l, v, r) => onNode }`. -/
private def onTree (onNode : Expr) : Expr :=
  .match (.var "t") .i64 [⟨.variant "Tree" "Leaf" [], [], none, .int 0⟩,
    ⟨.variant "Tree" "Node" [.bind "l", .bind "v", .bind "r"], ["l", "v", "r"], none, onNode⟩]

private def treeProgram (body : Expr) (arg : Expr) : Program :=
  ⟨⟨[], [tree], [treeFn "sum" body], [], [], [], [], []⟩, .raise (call "sum" arg),
    ⟨false, some .i64, [], [], none⟩, {}⟩

/-- `Node(Node(Leaf, 1, Leaf), 2, Node(Leaf, 3, Leaf))`. -/
private def three : Expr := node (node leaf (.int 1) leaf) (.int 2) (node leaf (.int 3) leaf)

/-- `fn sum(t: Tree) -> i64 { match t { Leaf => 0, Node(l, v, r) => sum(l) + v + sum(r) } }`:
each self-call passes a part that the pattern binds. -/
private def sumBody : Expr := onTree (add (add (call "sum" (.var "l")) (.var "v")) (call "sum" (.var "r")))

example : (treeProgram sumBody three).divFree = true := rfl
example : (treeProgram sumBody three).DivFree := Program.divFree_spec rfl
example : ((treeProgram sumBody three).runCopy 40).observe = .raised (.int 6) := rfl

/-- `let u = l; sum(u)`: a binding that holds a strict part holds one too. -/
example : (treeProgram (onTree (.letIn "u" (.variant "Tree" []) (.var "l") (call "sum" (.var "u"))))
    three).divFree = true := rfl

/-- `sum(t)`, `sum(Node(l, v, r))`, and `l = Leaf; sum(l)` don't descend. -/
example : (treeProgram (call "sum" (.var "t")) three).divFree = false := rfl
example : (treeProgram (onTree (call "sum" (node (.var "l") (.var "v") (.var "r")))) three).divFree =
    false := rfl
example : (treeProgram (onTree (.seq (.assign ⟨"l", []⟩ leaf) (call "sum" (.var "l")))) three).divFree =
    false := rfl

/-- `type Cell = { head: i64, rest: List }`, `type List = | Nil | Cons(Cell)` and `fn len(xs: List)`,
which calls itself on `c.rest`: a place made of fields, rooted in a strict part, is one too. -/
private def cell : RecordDecl := ⟨"Cell", [("head", .i64), ("rest", .variant "List" [])], []⟩

private def wrapped : Decls :=
  ⟨[cell], [⟨"List", [("Nil", []), ("Cons", [.record "Cell" []])], []⟩],
    [⟨"len", [], [], [⟨.let, "xs", .variant "List" [], none⟩], .i64, Row.pure,
      .match (.var "xs") .i64 [⟨.variant "List" "Nil" [], [], none, .int 0⟩,
        ⟨.variant "List" "Cons" [.bind "c"], ["c"], none, add (.int 1) (call "len" (.field (.var "c") "rest"))⟩],
      {}⟩], [], [], [], [], []⟩

example : Decls.rankedBy wrapped wrapped.rank wrapped.desc = true := rfl

/-- `for u in [l] { sum(u) }`: an element of a list is no strict part, and no variable has a
role inside a loop. -/
example : (treeProgram (onTree (.for "u" (.variant "Tree" []) (.list (.variant "Tree" []) [.var "l"])
    (call "sum" (.var "u")))) three).divFree = false := rfl

/-! ## Shrinking recursion -/

private def cmp (c : Cmp) (a b : Expr) : Expr := .op (.compare c .i64) [a, b]
private def sub (a b : Expr) : Expr := .op (.arith .sub .i64) [a, b]

/-- `fn count(n: i64) -> i64 { if test { 0 } else { count(step) } }`, and `count(5)`. -/
private def counting (test step : Expr) : Program :=
  ⟨⟨[], [], [fn "count" (.if test .i64 (.int 0) (call "count" step))], [], [], [], [], []⟩,
    .raise (call "count" (.int 5)), ⟨false, some .i64, [], [], none⟩, {}⟩

/-- `if n <= 0 { 0 } else { count(n - 1) }` shrinks: the `else` branch of `n <= 0` gives
`n > 0`. -/
example : (counting (cmp .le (.var "n") (.int 0)) (sub (.var "n") (.int 1))).divFree = true := rfl
example : ((counting (cmp .le (.var "n") (.int 0)) (sub (.var "n") (.int 1))).runCopy 40).observe =
    .raised (.int 0) := rfl

/-- `if n == 0 { 0 } else { count(n - 1) }` doesn't, nor does `count(n + 1)` after `n <= 0`. -/
example : (counting (cmp .eq (.var "n") (.int 0)) (sub (.var "n") (.int 1))).divFree = false := rfl
example : (counting (cmp .le (.var "n") (.int 0)) (add (.var "n") (.int 1))).divFree = false := rfl

/-- `fn go(i: i64, n: i64) -> i64 { if i < n { go(i + 1, n) } else { i } }`: the bound is a
parameter that every self-call passes unchanged. `go(i + 1, n - 1)` changes it. -/
private def going (next : Expr) : Program :=
  ⟨⟨[], [], [⟨"go", [], [], [⟨.let, "i", .i64, none⟩, ⟨.let, "n", .i64, none⟩], .i64, Row.pure,
      .if (cmp .lt (.var "i") (.var "n")) .i64
        (.call (.fnRef "go" [] []) [.value (add (.var "i") (.int 1)), .value next] .i64) (.var "i"),
      {}⟩], [], [], [], [], []⟩,
    .raise (.call (.fnRef "go" [] []) [.value (.int 0), .value (.int 3)] .i64),
    ⟨false, some .i64, [], [], none⟩, {}⟩

example : (going (.var "n")).divFree = true := rfl
example : ((going (.var "n")).runCopy 40).observe = .raised (.int 3) := rfl
example : (going (sub (.var "n") (.int 1))).divFree = false := rfl

private def lt (a b : Expr) : Expr := .op (.compare .lt .i64) [a, b]
private def step (x : Name) (o : Arith) (k : Int) : Expr := .assign ⟨x, []⟩ (.op (.arith o .i64) [.var x, .int k])

/-- `var i = 0; var s = 0; while i < n { s = s + i; i = i + 1 }; raise s`, with `n` given:
with `n = 10` it ends at fuel 18 and not 17, and with `n = 20` it needs more, as each
turn costs a fuel. -/
private def counted (n : Int) (cond : Expr) (body : Expr) : Program :=
  ⟨⟨[], [], [], [], [], [], [], []⟩, .letIn "n" .i64 (.int n) (.varIn "i" .i64 (.int 0) (.varIn "s" .i64 (.int 0)
    (.seq (.while cond body) (.raise (.var "s"))))), ⟨false, some .i64, [], [], none⟩, {}⟩

private def loopBody : Expr := .seq (.assign ⟨"s", []⟩ (add (.var "s") (.var "i"))) (step "i" .add 1)

example : (counted 10 (lt (.var "i") (.var "n")) loopBody).divFree = true := rfl
example : ((counted 10 (lt (.var "i") (.var "n")) loopBody).runCopy 18).observe = .raised (.int 45) := rfl
example : ((counted 10 (lt (.var "i") (.var "n")) loopBody).runCopy 17).observe = .outOfFuel := rfl
example : ((counted 20 (lt (.var "i") (.var "n")) loopBody).runCopy 18).observe = .outOfFuel := rfl

/-- `n > i`, the mirror, and `i < n && s < 100`, the first conjunct of a chain, count too. -/
example : (counted 10 (.op (.compare .gt .i64) [.var "n", .var "i"]) loopBody).divFree = true := rfl
example : (counted 10 (.if (lt (.var "i") (.var "n")) .bool (lt (.var "s") (.int 100)) (.bool false))
    loopBody).divFree = true := rfl

/-- `while i < n { i = i + 0 }`, `while i < n { if s < 0 { i = i + 1 } }`, a `continue`
before the step, a step away from the bound, and a body that writes `n` don't count. -/
example : (counted 10 (lt (.var "i") (.var "n")) (step "i" .add 0)).divFree = false := rfl
example : (counted 10 (lt (.var "i") (.var "n"))
    (.if (lt (.var "s") (.int 0)) .unit (step "i" .add 1) .unit)).divFree = false := rfl
example : (counted 10 (lt (.var "i") (.var "n"))
    (.seq (.if (lt (.var "s") (.int 0)) .unit .continue .unit) (step "i" .add 1))).divFree = false := rfl
example : (counted 10 (lt (.var "i") (.var "n")) (step "i" .sub 1)).divFree = false := rfl
example : (counted 10 (lt (.var "i") (.var "n")) (.seq (step "n" .add 1) (step "i" .add 1))).divFree = false :=
  rfl

end Stilt.Examples.Ends
