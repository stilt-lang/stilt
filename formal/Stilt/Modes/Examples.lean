import Stilt.Modes.Facts
import Stilt.Modes.Demands
import Stilt.Rows

/-!
# The required tests of modes.facts-suite

The facts that the model infers for programs of the facts suite
(`tests/facts/`), written in the calculus: lists of `i64` stand for every
copy-on-write type, `push(inout xs, x)` for a write, and `len(xs)` for a read.
Each expected mode comes from the rule cited, as the suite's do.
-/

namespace Stilt.ModesExamples

private def lst : Ty := .list .i64

private def thunk : Ty := .fn [] .i64 Row.pure

private def param (x : Name) (τ : Ty := lst) (mode : Mode := .let) : Param :=
  ⟨mode, x, τ, none⟩

private def v (x : Name) : Expr := .var x

private def ints (ns : List Int) : Expr := .list .i64 (ns.map .int)

private def call (f : Name) (args : List Expr) : Expr :=
  .call (.fnRef f [] []) (args.map .value) .i64

private def lam (body : Expr) : Expr := .closure [] .i64 Row.pure body

/-- `push(inout xs, x)`, a write of `xs`. -/
private def push (xs : Name) (x : Expr) : Expr :=
  .call (.fnRef "push" [] []) [.inout ⟨xs, []⟩, .value x] .unit

private def decl (name : Name) (ps : List Param) (body : Expr) (result : Ty := lst) : FnDecl :=
  ⟨name, [], [], ps, result, Row.pure, body, {}⟩

/-- The body of `grown(xs, x)`: `var out = xs; push(inout out, x); out`. -/
private def grownBody : Expr := .varIn "out" lst (v "xs") (.seq (push "out" (v "x")) (v "out"))

/-- `type Pair = { left: List<i64>, right: List<i64> }`, and the functions the
programs call: `len` reads, `push` writes, `grown` consumes its first
parameter, `run` calls its parameter once and `repeat` in a loop. -/
private def D : Decls :=
  ⟨[⟨"Pair", [("left", lst), ("right", lst)], []⟩], [],
    [decl "len" [param "xs"] (.int 0) .i64,
     decl "push" [param "xs" lst .inout, param "x" .i64]
       (.assign ⟨"xs", [.index (.int 0)]⟩ (v "x")) .unit,
     decl "grown" [param "xs", param "x" .i64] grownBody,
     decl "run" [param "f" thunk] (.call (v "f") [] .i64) .i64,
     decl "repeat" [param "f" thunk, param "xs"]
       (.for "i" .i64 (v "xs") (.call (v "f") [] .i64)) .unit,
     decl "tick" [param "f" thunk, param "n" .i64]
       (.if (.bool true) .i64 (.int 0) (call "tock" [v "f", v "n"])) .i64,
     decl "tock" [param "f" thunk, param "n" .i64]
       (.if (.bool true) .i64 (.int 0) (call "tick" [v "f", v "n"])) .i64,
     decl "ping" [param "f" thunk, param "n" .i64]
       (.if (.bool true) .i64 (.call (v "f") [] .i64) (call "pong" [v "f", v "n"])) .i64,
     decl "pong" [param "f" thunk, param "n" .i64]
       (.if (.bool true) .i64 (.call (v "f") [] .i64) (call "ping" [v "f", v "n"])) .i64], [], [], [], [], []⟩

private def M : ModeEnv := ⟨D, D.consumed, D.onceParams⟩

/-- The modes of the binding `b` of a body with parameters `ps`. -/
private def modes (b : Binder) (body : Expr) (ps : List Param := []) : Option Modes :=
  ((M.bodyFacts ps body).find? (·.binder == b)).map (·.modes)

/-! ## Consumption and the locality of parameters (values.consumed-parameters; modes.escaping) -/

/-- `grown` consumes `xs`, which it rebinds with `var`. It passes `x` to
`push`, which stores it, so it consumes `x` too, but `x` is a scalar, whose
locality is `local` (modes.escaping). -/
example : D.consumed "grown" 0 = true := by decide

example : (modes (.param "x") grownBody [param "xs", param "x" .i64]).map (·.locality) =
    some .local := by decide

/-- `len` reads its parameter, and `push` takes it `inout`. -/
example : (D.consumed "len" 0, D.consumed "push" 0) = (false, false) := by decide

/-- A parameter's locality is its consumption: returned, stored, captured or
passed to a consumed parameter, it escapes; read, it is local. -/
example : (modes (.param "xs") (v "xs") [param "xs"]).map (·.locality) = some .escapes := by
  decide

example : (modes (.param "xs") (.record "Pair" [] [("left", v "xs"), ("right", ints [])])
    [param "xs"]).map (·.locality) = some .escapes := by decide

example : (modes (.param "xs") (lam (call "len" [v "xs"])) [param "xs"]).map (·.locality) =
    some .escapes := by decide

example : (modes (.param "xs") (call "grown" [v "xs", .int 1]) [param "xs"]).map (·.locality) =
    some .escapes := by decide

example : (modes (.param "xs") (call "len" [v "xs"]) [param "xs"]).map (·.locality) =
    some .local := by decide

/-! ## Locality (modes.escaping and modes.not-escaping) -/

/-- `let xs = [1]; e`, with `e` the rest of the body. -/
private def withXs (e : Expr) : Expr := .letIn "xs" lst (ints [1]) e

/-- The locality of `xs` in `let xs = [1]; e`. -/
private def xsLocality (e : Expr) : Option Locality :=
  (modes (.let "xs") (withXs e)).map (·.locality)

/-- Returned, raised, stored in a record, a list or a variant, assigned into
another place, captured by a returned closure, or passed to a consumed
parameter: each escapes. -/
example : xsLocality (v "xs") = some .escapes := by decide

example : xsLocality (.raise (v "xs")) = some .escapes := by decide

example : xsLocality (.seq (.record "Pair" [] [("left", v "xs"), ("right", ints [])]) (.int 0)) =
    some .escapes := by decide

example : xsLocality (.seq (.list lst [v "xs"]) (.int 0)) = some .escapes := by decide

example : xsLocality (.seq (.variant "Option" [] "Some" [v "xs"]) (.int 0)) = some .escapes := by
  decide

example : xsLocality (.varIn "m" (.list lst) (.list lst [])
    (.seq (.assign ⟨"m", [.index (.int 0)]⟩ (v "xs")) (.int 0))) = some .escapes := by decide

example : xsLocality (.letIn "f" thunk (lam (call "len" [v "xs"])) (v "f")) = some .escapes := by
  decide

example : xsLocality (.seq (call "grown" [v "xs", .int 2]) (.int 0)) = some .escapes := by decide

/-- Assigned to a part of another binding, or to an `inout` parameter: each
escapes, as through an index. -/
example : xsLocality (.varIn "r" (.record "Pair" []) (.record "Pair" [] [("left", ints []),
    ("right", ints [])]) (.seq (.assign ⟨"r", [.field "left"]⟩ (v "xs")) (.int 0))) =
    some .escapes := by decide

example : (modes (.let "xs") (withXs (.assign ⟨"t", []⟩ (v "xs"))) [param "t" lst .inout]).map
    (·.locality) = some .escapes := by decide

/-- Assigned to the whole of another local, it is copied, and stays local. -/
example : xsLocality (.varIn "ws" lst (ints [0])
    (.seq (.assign ⟨"ws", []⟩ (v "xs")) (call "len" [v "ws"]))) = some .local := by decide

/-- Passed `inout`, captured by a closure only called, only read, or copied
by `var`: each is local. -/
example : xsLocality (.varIn "ys" lst (v "xs") (.seq (push "ys" (.int 2)) (call "len" [v "xs"]))) =
    some .local := by decide

example : xsLocality (.letIn "f" thunk (lam (call "len" [v "xs"])) (.call (v "f") [] .i64)) =
    some .local := by decide

example : xsLocality (call "len" [v "xs"]) = some .local := by decide

/-- A scalar is local whatever it does (modes.escaping). -/
example : (modes (.let "n") (.letIn "n" .i64 (.int 1) (v "n"))).map (·.locality) =
    some .local := by decide

/-! ## Uniqueness (modes.copy-on-write-types, modes.copies and modes.shared-writes) -/

/-- The uniqueness of `xs` in `var xs = [1]; e`. -/
private def xsUniqueness (e : Expr) : Option Uniqueness :=
  (modes (.var "xs") (.varIn "xs" lst (ints [1]) e)).map (·.uniqueness)

/-- `len(xs) + len(ys)`, which reads both after the write. -/
private def both : Expr := .seq (call "len" [v "xs"]) (call "len" [v "ys"])

/-- Written after a `let` copies it, after a closure captures it, after a
literal holds it, and after a lost reuse, each shared. -/
example : xsUniqueness (.letIn "ys" lst (v "xs") (.seq (push "xs" (.int 2)) both)) =
    some .shared := by decide

example : xsUniqueness (.letIn "f" thunk (lam (call "len" [v "xs"]))
    (.seq (push "xs" (.int 2)) (.call (v "f") [] .i64))) = some .shared := by decide

example : xsUniqueness (.letIn "p" (.record "Pair" []) (.record "Pair" [] [("left", v "xs"),
    ("right", ints [])]) (.seq (push "xs" (.int 2)) (.int 0))) = some .shared := by decide

example : xsUniqueness (.letIn "ys" lst (call "grown" [v "xs", .int 2])
    (.seq (push "xs" (.int 3)) (call "len" [v "ys"]))) = some .shared := by decide

/-- Written inside a loop whose body copies it later, shared. -/
example : xsUniqueness (.for "i" .i64 (ints [0, 1])
    (.seq (push "xs" (v "i")) (.letIn "ys" lst (v "xs") (call "len" [v "ys"])))) =
    some .shared := by decide

/-- Written after the copy's scope ends, after the whole binding is assigned
again, or after its last use is passed on: each unique. -/
example : xsUniqueness (.seq (.letIn "ys" lst (v "xs") (call "len" [v "ys"]))
    (push "xs" (.int 2))) = some .unique := by decide

example : xsUniqueness (.letIn "ys" lst (v "xs")
    (.seq (.assign ⟨"xs", []⟩ (ints [5])) (.seq (push "xs" (.int 2)) both))) =
    some .unique := by decide

example : xsUniqueness (.letIn "ys" lst (call "grown" [v "xs", .int 2]) (call "len" [v "ys"])) =
    some .unique := by decide

/-- A loop that gives the variable a new value from its last one loses no
reuse, so the write before it in the next turn is unique. -/
example : xsUniqueness (.for "i" .i64 (ints [0, 1])
    (.seq (push "xs" (v "i")) (.assign ⟨"xs", []⟩ (call "grown" [v "xs", v "i"])))) =
    some .unique := by decide

/-- `copy_of_a_copy`: a copy of a copy is a copy of the binding, held by
whatever holds it, so `ws`, which holds a copy of `ys`'s copy after the block,
shares the write. -/
example : xsUniqueness (.varIn "ws" lst (ints [0])
    (.seq (.if (v "flag") .unit (.letIn "ys" lst (v "xs") (.assign ⟨"ws", []⟩ (v "ys"))) .unit)
      (.seq (push "xs" (.int 2)) (call "len" [v "ws"])))) = some .shared := by decide

/-- A copy of a copy made before the whole binding is assigned again shares
only the old value. -/
example : xsUniqueness (.letIn "ys" lst (v "xs") (.seq (.assign ⟨"xs", []⟩ (ints [5]))
    (.varIn "ws" lst (ints [0]) (.seq (.assign ⟨"ws", []⟩ (v "ys"))
      (.seq (push "xs" (.int 2)) (call "len" [v "ws"])))))) = some .unique := by decide

/-- A copy of one part doesn't share another. -/
example : (modes (.var "p") (.varIn "p" (.record "Pair" []) (v "q")
    (.letIn "l" lst (.field (v "p") "left")
      (.seq (.call (.fnRef "push" [] []) [.inout ⟨"p", [.field "right"]⟩, .value (.int 1)] .unit)
        (call "len" [v "l"]))))).map (·.uniqueness) = some .unique := by decide

/-! ### Copies held as a whole value (modes.shared-writes) -/

/-- The uniqueness of `ys` in `let xs = [1]; var ys = xs; e`. -/
private def ysUniqueness (e : Expr) : Option Uniqueness :=
  (modes (.var "ys") (withXs (.varIn "ys" lst (v "xs") e))).map (·.uniqueness)

/-- `holds_a_copy`: `ys` is written while `xs`, whose value it copies, is read
after the write, so the write is shared; `copy_read_no_more`: it is unique
once nothing reads `xs` again. -/
example : ysUniqueness (.seq (push "ys" (.int 2)) both) = some .shared := by decide

example : ysUniqueness (.seq (push "ys" (.int 2)) (call "len" [v "ys"])) =
    some .unique := by decide

/-- `another_copy`: another copy of `xs`, read after the write, shares it too. -/
example : (modes (.var "ys") (withXs (.letIn "zs" lst (v "xs") (.varIn "ys" lst (v "xs")
    (.seq (push "ys" (.int 2)) (call "len" [v "zs"])))))).map (·.uniqueness) =
    some .shared := by decide

/-- `read_in_a_loop`: a loop around the write that reads `xs` reads it again. -/
example : (modes (.var "ys") (withXs (.for "i" .i64 (ints [0, 1])
    (.seq (call "len" [v "xs"]) (.varIn "ys" lst (v "xs") (push "ys" (.int 2))))))).map
      (·.uniqueness) = some .shared := by decide

/-- `original_replaced`: assigning the whole of `xs` before the write replaces
what it read. -/
example : (modes (.var "ys") (.varIn "xs" lst (ints [1]) (.varIn "ys" lst (v "xs")
    (.seq (.assign ⟨"xs", []⟩ (ints [5])) (.seq (push "ys" (.int 2)) both))))).map
      (·.uniqueness) = some .unique := by decide

/-- A copy assigned to the whole of `ys` counts as one bound, and one that an
assignment of its whole replaced no longer does. -/
example : (modes (.var "ys") (withXs (.varIn "ys" lst (ints [0])
    (.seq (.assign ⟨"ys", []⟩ (v "xs")) (.seq (push "ys" (.int 2)) both))))).map
      (·.uniqueness) = some .shared := by decide

example : ysUniqueness (.seq (.assign ⟨"ys", []⟩ (ints [5])) (.seq (push "ys" (.int 2)) both)) =
    some .unique := by decide

/-- A parameter's copy: `held` of `promises/copies.lt`. -/
example : (modes (.var "ys") (.varIn "ys" lst (v "xs") (.seq (push "ys" (.int 1)) both))
    [param "xs"]).map (·.uniqueness) = some .shared := by decide

/-! ### Copies held at a place inside a value (modes.shared-writes) -/

/-- A push onto the place `path` of `y`. -/
private def pushAt (y : Name) (path : List Projection) : Expr :=
  .call (.fnRef "push" [] []) [.inout ⟨y, path⟩, .value (.int 1)] .unit

/-- The uniqueness of `p` in `let xs = [1]; var p = Pair { left: l, right: [] }; e`. -/
private def pUniqueness (l e : Expr) : Option Uniqueness :=
  (modes (.var "p") (withXs (.varIn "p" (.record "Pair" [])
    (.record "Pair" [] [("left", l), ("right", ints [])]) e))).map (·.uniqueness)

/-- `in_a_field`: a write inside the field that holds the copy is shared while
`xs` is read after it; one beside it, to `right`, is not. -/
example : pUniqueness (v "xs") (.seq (pushAt "p" [.field "left"]) (call "len" [v "xs"])) =
    some .shared := by decide

example : pUniqueness (v "xs") (.seq (pushAt "p" [.field "right"]) (call "len" [v "xs"])) =
    some .unique := by decide

/-- `in_a_part`: a copy assigned to a part is at that place; `beside`: an
assignment to the place replaces the copy there. -/
example : pUniqueness (ints []) (.seq (.assign ⟨"p", [.field "left"]⟩ (v "xs"))
    (.seq (pushAt "p" [.field "left"]) (call "len" [v "xs"]))) = some .shared := by decide

example : pUniqueness (v "xs") (.seq (.assign ⟨"p", [.field "left"]⟩ (ints [5]))
    (.seq (pushAt "p" [.field "left"]) (call "len" [v "xs"]))) = some .unique := by decide

/-- `in_a_list`: a write inside an element of a list that holds the copy is
shared; a push onto the list itself writes no copy. -/
private def lsUniqueness (e : Expr) : Option Uniqueness :=
  (modes (.var "ls") (withXs (.varIn "ls" (.list lst) (.list lst [v "xs"]) e))).map
    (·.uniqueness)

example : lsUniqueness (.seq (pushAt "ls" [.index (.int 0)]) (call "len" [v "xs"])) =
    some .shared := by decide

example : lsUniqueness (.seq (.call (.fnRef "push" [] []) [.inout ⟨"ls", []⟩, .value (ints [])] .unit)
    (call "len" [v "xs"])) = some .unique := by decide

/-! ### Copies of copies held in parts (modes.copies and modes.shared-writes)

`modes/copies_of_held_parts.lt`: a binding that copies the part of a value
that holds a copy of `a` holds a copy of `a` itself, so a write to it is
shared while `a` is read after it; a part beside the copy holds none of it. -/

/-- `Pair { left: l, right: r }`. -/
private def pair (l r : Expr) : Expr := .record "Pair" [] [("left", l), ("right", r)]

/-- `push(inout z, 1); len(z) + rest`. -/
private def writeZ (rest : Expr) : Expr :=
  .seq (push "z" (.int 1)) (.seq (call "len" [v "z"]) rest)

/-- The uniqueness of `z` in a body with parameters `ps`. -/
private def zUniqueness (body : Expr) (ps : List Param := [param "a"]) : Option Uniqueness :=
  (modes (.var "z") body ps).map (·.uniqueness)

/-- `through_a_field` and `through_an_index`. -/
example : zUniqueness (.letIn "p" (.record "Pair" []) (pair (v "a") (ints []))
    (.varIn "z" lst (.field (v "p") "left") (writeZ (call "len" [v "a"])))) =
    some .shared := by decide

example : zUniqueness (.letIn "xs" (.list lst) (.list lst [v "a"])
    (.varIn "z" lst (.index (v "xs") (.int 0)) (writeZ (call "len" [v "a"])))) =
    some .shared := by decide

/-- `through_a_pattern`, and `through_if_let` on a tuple: a binder holds the
copy at the place of the value it matches; one beside it holds none. -/
example : zUniqueness (.letIn "p" (.record "Pair" []) (pair (v "a") (ints []))
    (.match (v "p") .i64 [⟨.record "Pair" [("left", .bind "left"), ("right", .wild)], ["left"], none,
      .varIn "z" lst (v "left") (writeZ (call "len" [v "a"]))⟩])) = some .shared := by decide

example : zUniqueness (.letIn "p" (.tuple [.list lst, .i64])
    (.op .tuple [.list lst [v "a"], .int 1]) (.match (v "p") .i64 [⟨.tuple [.list [.bind "l"] .exact, .wild], ["l"], none,
      .varIn "z" lst (v "l") (writeZ (call "len" [v "a"]))⟩, ⟨.wild, [], none, .int 0⟩])) =
    some .shared := by decide

example : zUniqueness (.letIn "p" (.record "Pair" []) (pair (v "a") (ints []))
    (.match (v "p") .i64 [⟨.record "Pair" [("left", .wild), ("right", .bind "right")], ["right"], none,
      .varIn "z" lst (v "right") (writeZ (call "len" [v "a"]))⟩])) = some .unique := by decide

/-- `through_a_loop`, `through_an_assignment` and `after_a_loop`: a copy comes
into a binding by `var`, by assignment, or by a `for`'s element. -/
example : zUniqueness (.letIn "xs" (.list lst) (.list lst [v "a"])
    (.seq (.for "y" lst (v "xs") (.varIn "z" lst (v "y") (writeZ .unit)))
      (call "len" [v "a"]))) = some .shared := by decide

example : zUniqueness (.letIn "y" lst (v "a") (.varIn "z" lst (ints [])
    (.seq (.assign ⟨"z", []⟩ (v "y")) (writeZ (call "len" [v "a"]))))) = some .shared := by
  decide

example : zUniqueness (.letIn "xs" (.list lst) (.list lst [v "a"]) (.varIn "z" lst (ints [])
    (.seq (.for "y" lst (v "xs") (.assign ⟨"z", []⟩ (v "y")))
      (writeZ (call "len" [v "a"]))))) = some .shared := by decide

/-- `inside_the_copy`: a part inside the copy, here held by a tuple's field,
is a copy of a part of `a`. -/
example : zUniqueness (.letIn "t" (.tuple [.record "Pair" [], .i64]) (.op .tuple [v "a", .int 1])
    (.varIn "z" lst (.field (.field (v "t") "0") "left")
      (writeZ (call "len" [.field (v "a") "left"])))) [param "a" (.record "Pair" [])] =
    some .shared := by decide

/-- `var a = q; var z = []; { let p = Pair { left: a, right: [2] }; z = p.f };
push(inout a, 1); len(z) + len(a)`. -/
private def heldAfter (f : Name) : Expr :=
  .varIn "a" lst (v "q") (.varIn "z" lst (ints [])
    (.seq (.letIn "p" (.record "Pair" []) (pair (v "a") (ints [2]))
        (.assign ⟨"z", []⟩ (.field (v "p") f)))
      (.seq (push "a" (.int 1)) (.seq (call "len" [v "z"]) (call "len" [v "a"])))))

/-- `beside_the_copy`: once `p` has gone, `z = p.right` holds nothing of `a`,
and the write to `a` is unique; `holding_the_copy`: `z = p.left` still holds a
copy of `a`, and the write is shared. -/
example : (modes (.var "a") (heldAfter "right") [param "q"]).map (·.uniqueness) =
    some .unique := by decide

example : (modes (.var "a") (heldAfter "left") [param "q"]).map (·.uniqueness) =
    some .shared := by decide

/-- A scalar is unique: nothing is copied on write. -/
example : (modes (.var "n") (.varIn "n" .i64 (.int 0) (.letIn "m" .i64 (v "n")
    (.seq (.assign ⟨"n", []⟩ (.int 1)) (v "m"))))).map (·.uniqueness) =
    some .unique := by decide

/-! ## Once (modes.once-closures and modes.once-parameters) -/

/-- The once point of `f` in `let f = || 1; e`. -/
private def fOnce (e : Expr) : Option (Option Once) :=
  (modes (.let "f") (.letIn "f" thunk (lam (.int 1)) e)).map (·.once)

/-- A closure called where it is written, bound and called once, or passed to
a `once` parameter, is `once`. -/
example : modes .closure (.call (lam (.int 1)) [] .i64) = some ⟨.local, .unique, some .once,
    .portable, .calm⟩ := by decide

example : fOnce (.call (v "f") [] .i64) = some (some .once) := by decide

example : (modes .closure (call "run" [lam (.int 2)])).map (·.once) = some (some .once) := by
  decide

/-- Called twice, in a loop, inside another closure, stored, or passed to a
`many` parameter: each `many`. -/
example : fOnce (.seq (.call (v "f") [] .i64) (.call (v "f") [] .i64)) = some (some .many) := by decide

example : fOnce (.for "i" .i64 (ints [1]) (.call (v "f") [] .i64)) = some (some .many) := by decide

example : fOnce (.letIn "g" thunk (lam (.call (v "f") [] .i64)) (.call (v "g") [] .i64)) =
    some (some .many) := by decide

example : fOnce (.list thunk [v "f"]) = some (some .many) := by decide

example : fOnce (call "repeat" [v "f", ints [1]]) = some (some .many) := by decide

/-- A parameter called once is `once`; one called in a loop is `many`. -/
example : (D.onceParams "run" 0, D.onceParams "repeat" 0) = (true, false) := by decide

/-- A recursive group that calls a parameter once in each function keeps it
`once`; one that calls it twice makes it `many`. -/
example : (D.onceParams "tick" 0, D.onceParams "tock" 0) = (true, true) := by decide +kernel

example : (D.onceParams "ping" 0, D.onceParams "pong" 0) = (false, false) := by decide +kernel

/-! ## The thread axes and `show` (modes.fixed-values, modes.contended-values, modes.mode-crossing and modes.show) -/

/-- No binding of this core body is `fixed` or `contended`. -/
example : (M.bodyFacts [param "xs"] grownBody).all
    (fun f => f.modes.portability == .portable && f.modes.contention == .calm) = true := by decide

/-- `grown` prints `consumes xs` for its parameter and `escapes` for `out`, its
result, and nothing else: one word for each mode other than the default, as the annotations of
the facts suite give them (modes.facts-suite), and neither `fixed` nor `contended`, as no binding
of a core module is. -/
theorem grown_words : (M.bodyFacts [param "xs", param "x" .i64] grownBody).map Fact.words =
    [["consumes"], [], ["escapes"]] := by decide

/-- A closure called where it is written prints `once` alone. -/
example : (M.bodyFacts [] (.call (lam (.int 1)) [] .i64)).map Fact.words = [["once"]] := by decide

/-- `type Box = { cell: Shared<i64> }` and `type Tree = { kids: List<Tree> }`: a record whose
field is a `Shared<T>` holds one, and a recursive type that holds none is no reason. -/
private def threadDecls : Decls :=
  ⟨[⟨"Box", [("cell", .shared .i64)], []⟩, ⟨"Tree", [("kids", .list (.record "Tree" []))], []⟩],
    [], [], [], [], [], [], []⟩

private def TM : ModeEnv := ⟨threadDecls, threadDecls.consumed, threadDecls.onceParams⟩

example : (threadDecls.contended (.record "Box" []), threadDecls.contended (.record "Tree" []),
    threadDecls.contended (.list (.tuple [.i64, .shared .str])),
    threadDecls.contended (.fn [(.let, .shared .i64)] .i64 Row.pure),
    threadDecls.contended (.fn [(.inout, .shared .i64)] .i64 Row.pure)) =
    (true, false, true, false, true) := by decide

/-- A parameter of a type that holds a `Shared<T>` is `contended`, and so is a closure literal
that captures one, bound or not; one that captures nothing is `calm`, and so is a binding of a
value read from the handle (modes.contended-values). -/
example : (TM.bodyFacts [param "b" (.record "Box" [])]
    (.letIn "f" thunk (lam (.field (v "b") "cell"))
      (.seq (.call (lam (.int 1)) [] .i64) (.call (lam (v "b")) [] .i64)))).map Fact.words =
    [["contended"], ["contended"], ["once"], ["once", "contended"]] := by decide

/-- A closure literal that captures a view is `fixed` (modes.fixed-values and views.fixed). -/
example : (TM.bodyFacts [param "w" (.view lst)] (.call (lam (v "w")) [] .i64)).map Fact.words =
    [["fixed"], ["once", "fixed"]] := by decide

/-- `Shared.new` demands a `portable` value (modes.demands, E0432): a view is none, nor is a
closure literal that captures one, bound or not; a closure that captures a list is, and so is a
handle, since `Shared<T>` is `portable`. -/
example : ((Expr.op (.world (.sharedNew (.view lst))) [v "w"]).demandsMet D [param "w" (.view lst)],
    (Expr.op (.world (.sharedNew thunk)) [lam (v "w")]).demandsMet D [param "w" (.view lst)],
    (Expr.letIn "f" thunk (lam (v "w")) (.op (.world (.sharedNew thunk)) [v "f"])).demandsMet D
      [param "w" (.view lst)],
    (Expr.op (.world (.sharedNew thunk)) [lam (v "xs")]).demandsMet D [param "xs"],
    (Expr.op (.world (.sharedNew (.shared .i64))) [v "a"]).demandsMet D [param "a" (.shared .i64)]) =
    (false, false, false, true, true) := by decide

/-- A `match` arm's binder holds what the matched value holds: a closure that captures one of
a calm value's is calm, and one of a contended value's contended. -/
example : (TM.bodyFacts [param "b" (.record "Box" []), param "t" (.record "Tree" [])]
    (.seq (.match (v "t") .i64 [⟨.bind "s", ["s"], none, .call (lam (v "s")) [] .i64⟩])
      (.match (v "b") .i64 [⟨.bind "c", ["c"], none, .call (lam (v "c")) [] .i64⟩]))).map
    Fact.words = [["contended"], [], ["once"], ["once", "contended"]] := by decide

end Stilt.ModesExamples
