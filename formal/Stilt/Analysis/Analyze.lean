import Stilt.Analysis.Ops
import Stilt.Analysis.Count

/-!
# The analysis of a body

`an L d F e`: what the analysis gives the expression `e` evaluated where the facts `F` hold,
with `d` values read and not yet used, in a body that is large when `L` says so. The facts flow
through the expression in the order of evaluation (facts.analysis-order): each operand's value
is pushed as a value read and not yet used before the next is evaluated, so an operation checks
the values its operands gave where they were evaluated, and the facts where it happens.

Literals, bindings, conversions, `+`, `-`, `*`, `/`, `%`, `-a`, comparisons, `!`, lengths,
`push`, list literals, indexes, field reads, `let`, `var`, assignments to a binding and stores
through `xs[i]`, blocks, `if`, `break`, `continue`, `return` and `raise` are analysed as
`Stilt.Analysis` states them. A `while`, a `loop` and a `for` are analysed from head facts
found by dropping those a turn of the body doesn't give back (`loopHead`), when they check:
the facts before the loop give them, and every turn gives them back. Every other form is analysed as code that keeps the facts on the
bindings it doesn't write, and its parts from no fact at all, which is all a fact set can say
of them that holds. A closure literal's body, and the body of a function it calls, are analysed
on their own, where they are called (`Expr.verified`).

A mark `Form.proved ks` says that the operation it holds can't panic with the kinds `ks`; the
analysis proves it or doesn't (`Res.ok`).
-/

namespace Stilt

/-- The facts closed once added, and in a large body only their bounds kept (facts.large-bodies). -/
def Facts.tidy (L : Bool) (F : Facts) : Facts := if L then F.close.onlyBounds else F.close

/-- The value bound or assigned to `x`: `res` becomes `x`'s value and `reslen` its length, once
every earlier fact on `x` is dropped (facts.bindings-and-assignments). -/
def Facts.assignTo (F : Facts) (x : Name) : Facts :=
  (F.restrict fun t => t.name? != some x).map fun t =>
    match t with
    | .res => .val x
    | .reslen => .len x
    | t => t

/-- The facts that every outcome of a scope keeps once its binding of `x` ends. -/
def Facts.unbind (F : Facts) (x : Name) : Facts := F.restrict fun t => t.name? != some x

/-- What the operands of an operation give, pushed one after another as values read and not yet
used from the `d`th: the facts after the last, those at each `break` and `continue` that leaves
them, their linear forms, and whether every mark in them is proved. -/
structure Ops where
  post : Facts
  brk : Facts
  cont : Facts
  lins : List (Option (Term × Int))
  ok : Bool

/-- Code that ends where the facts `G` hold, and never jumps. -/
def Res.pure (G : Facts) : Res := { post := G, tt := G, ff := G, brk := .bot, cont := .bot, ok := true }

/-- The linear form of an operation's value (facts.linear-forms): `e + c`, `c + e` and `e − c`
for `c` a literal, a conversion's, and a list binding's length. -/
def linOp (o : Op) (es : List Expr) (lins : List (Option (Term × Int))) : Option (Term × Int) :=
  match o, es, lins with
  | .arith .add _, [_, .int c], [some (t, k), _] => some (t, k + c)
  | .arith .add _, [.int c, _], [_, some (t, k)] => some (t, k + c)
  | .arith .sub _, [_, .int c], [some (t, k), _] => some (t, k - c)
  | .convert _ _, _, [l] => l
  | .list .len, [.var xs], _ => some (.len xs, 0)
  | _, _, _ => none

/-- What an operation gives once its operands are pushed: a comparison its facts where true and
where false (facts.conditions), any other its value's facts (`opValFacts`). -/
def opRes (L : Bool) (d : Nat) (o : Op) (es : List Expr) (os : Ops) : Res :=
  let G := os.post.noRes
  match o, os.lins with
  | .compare c _, [_, _] =>
    { post := (G.tidy L).within d, tt := ((cmpFacts c d os.lins G true).tidy L).within d,
      ff := ((cmpFacts c d os.lins G false).tidy L).within d, brk := os.brk, cont := os.cont,
      ok := os.ok }
  | _, _ =>
    let H := ((opValFacts o d os.lins G).tidy L).within d
    { post := H, tt := H, ff := H, brk := os.brk, cont := os.cont, lin := linOp o es os.lins,
      lo := os.post.linAt d (linOf os.lins 0), hi := os.post.linAt (d + 1) (linOf os.lins 1),
      ok := os.ok }

/-- A list literal's value: its length the number of its elements (facts.bindings-and-assignments). -/
def listRes (L : Bool) (d n : Nat) (os : Ops) : Res :=
  let H := (((os.post.noRes.insert ⟨.reslen, .zero, n⟩).insert ⟨.zero, .reslen, -n⟩).tidy L).within d
  { post := H, tt := H, ff := H, brk := os.brk, cont := os.cont, ok := os.ok }

/-- What `a[i]` gives once `a`'s value is pushed `d`th and `i`'s `d + 1`th. -/
def indexRes (d : Nat) (ra ri : Res) : Res :=
  let H := ri.post.noRes.within d
  { post := H, tt := H, ff := H, brk := ra.brk.join (ri.brk.within d),
    cont := ra.cont.join (ri.cont.within d), ok := ra.ok && ri.ok }

/-- Whether an index read is proved: `a` is a list binding, and the facts give `0 ≤ i` and
`i ≤ ℓ − 1`, for `ℓ` the length `a` had where it was evaluated (facts.proved-indexes,
facts.analysis-order). -/
def indexProved (a : Expr) (d : Nat) (ri : Res) : Bool :=
  match a with
  | .var _ => (ri.post.push (d + 1)).indexOk (.opnd (d + 1)) (.opndLen d)
  | _ => false

/-- What `x[i] = v` gives once `i`'s value is pushed `d`th: `x`'s value and length are as they
were, a store through `xs[i]` giving no new length (facts.writes-through-calls). -/
def storeRes (d : Nat) (ri rv : Res) : Res :=
  let H := rv.post.noRes.within d
  { post := H, tt := H, ff := H, brk := ri.brk.join (rv.brk.within d),
    cont := ri.cont.join (rv.cont.within d), ok := ri.ok && rv.ok }

/-- Code that leaves by a jump: no fact where it ends. -/
def Res.leaves (brk cont : Facts) (ok : Bool) : Res :=
  { post := .bot, tt := .bot, ff := .bot, brk, cont, ok }

/-- A binding's scope: the facts of its body without those on its name, at its end and at each
jump that leaves it. -/
def scopeRes (x : Name) (r b : Res) : Res :=
  { post := b.post.unbind x, tt := b.tt.unbind x, ff := b.ff.unbind x,
    brk := r.brk.join (b.brk.unbind x), cont := r.cont.join (b.cont.unbind x), ok := r.ok && b.ok }

/-- One expression after another: the second's facts, the jumps of both. -/
def seqRes (a b : Res) : Res :=
  { b with brk := a.brk.join b.brk, cont := a.cont.join b.cont, ok := a.ok && b.ok }

/-- An `if`: the join of its branches, each from its condition's facts (facts.joins). -/
def ifRes (c a b : Res) : Res :=
  { post := a.post.join b.post, tt := a.tt.join b.tt, ff := a.ff.join b.ff,
    brk := c.brk.join (a.brk.join b.brk), cont := c.cont.join (a.cont.join b.cont),
    ok := c.ok && a.ok && b.ok }

/-- The facts of `C` that `S` gives, all of them where `S` is contradictory. -/
def Facts.keptBy (C S : Facts) : Facts :=
  if S.contra then C else
    { diffs := C.diffs.filter fun d => S.entails ⟨[d], []⟩,
      nonzero := C.nonzero.filter fun t => S.entails ⟨[], [t]⟩ }

/-- A loop's candidate head facts: from `C`, the facts that a turn of the loop doesn't keep
dropped, `k` times over, where `turn` gives the facts at the end of a turn from those at its
head. -/
def loopHead (turn : Facts → Facts) : Nat → Facts → Facts
  | 0, C => C
  | k + 1, C => loopHead turn k (C.keptBy (turn C).close)

/-- A `while` whose head facts are `I`, from the facts `F` before it, its condition analysed
from `I` and its body from the condition's facts where true: where `F` gives `I` and each turn
of the body keeps it, the loop ends where its condition is false or by a `break`; otherwise,
`fallback`. -/
def whileRes (F I : Facts) (rc rb fallback : Res) : Res :=
  if F.close.entails I && (rb.post.noRes.join rb.cont).close.entails I then
    let P := rc.ff.noRes.join rb.brk
    { post := P, tt := P, ff := P, brk := rc.brk, cont := rc.cont, ok := rc.ok && rb.ok }
  else fallback

/-- A `loop` whose head facts are `I`, its body analysed from them: where `F` gives `I` and each
turn of the body keeps it, the loop ends by a `break`; otherwise, `fallback`. -/
def loopRes (F I : Facts) (rb fallback : Res) : Res :=
  if F.close.entails I && (rb.post.noRes.join rb.cont).close.entails I then
    { post := rb.brk, tt := rb.brk, ff := rb.brk, brk := .bot, cont := .bot, ok := rb.ok }
  else fallback

/-- A `for` over the values of an iterable, from the facts `G` after the iterable, its head
facts `I`, on no term of its variable `x`, and its body analysed from them: where `G` gives `I`
and each turn of the body keeps it, the loop ends where `I` holds or a `break`'s facts do;
otherwise, `fallback`. -/
def forRes (x : Name) (G I : Facts) (re rb fallback : Res) : Res :=
  if G.close.entails I && ((rb.post.noRes.join rb.cont).unbind x).close.entails I then
    let P := I.join (rb.brk.unbind x)
    { post := P, tt := P, ff := P, brk := re.brk, cont := re.cont, ok := re.ok && rb.ok }
  else fallback

/-- Whether an iterable is a range, `a..b` or `a..=b`. -/
def Expr.isRange : Expr → Bool
  | .op (.list (.range _)) _ => true
  | _ => false

/-- Whether an iterable is a range `a..b`. -/
def Expr.isExclusiveRange : Expr → Bool
  | .op (.list (.range false)) _ => true
  | _ => false

/-- Whether a term of a range's bound stays put through the turns of a `for` whose variable is
`x` and whose body writes `W` and changes the length of `Ls`: zero, or a binding's value or
length that the body doesn't write, or, for the second bound, `lower` false, a length the body
doesn't change. -/
def Term.steady (x : Name) (W Ls : List Name) (lower : Bool) : Term → Bool
  | .zero => true
  | .val y => decide (y ≠ x) && decide (y ∉ W)
  | .len y => decide (y ≠ x) && (if lower then decide (y ∉ W) else decide (y ∉ Ls))
  | _ => false

/-- The facts on a `for`'s variable `x` over a range (facts.for-loops): no less than its first
bound `lo`, and below its second `hi`, read on each value the loop runs its body on. -/
def Facts.forRange (C : Facts) (x : Name) (lo hi : Option (Term × Int)) : Facts :=
  let C := match lo with
    | some (t, c) => C.insert ⟨t, .val x, -c⟩
    | none => C
  match hi with
  | some (t, c) => C.insert ⟨.val x, t, c - 1⟩
  | none => C

mutual

/-- What the analysis gives `e` where the facts `F` hold, with `d` values read and not yet used
(facts.terms, facts.linear-forms, facts.bindings-and-assignments, facts.conditions,
facts.joins and facts.paths-that-leave). -/
def an (L : Bool) (d : Nat) (F : Facts) : Expr → Res
  | .var x | .move x =>
    let G := ((((F.noRes.insert ⟨.res, .val x, 0⟩).insert ⟨.val x, .res, 0⟩).insert
      ⟨.reslen, .len x, 0⟩).insert ⟨.len x, .reslen, 0⟩).tidy L
    { Res.pure G with lin := some (.val x, 0) }
  | .int k =>
    let G := (F.noRes.equate .zero k).insert ⟨.reslen, .zero, 0⟩
    { Res.pure ((if k = 0 then G else G.addNonzero .res).tidy L) with lin := some (.zero, k) }
  | .bool b =>
    let G := F.noRes
    { Res.pure G with tt := if b then G else .bot, ff := if b then .bot else G }
  | .unit | .fnRef .. | .method .. | .closure .. => Res.pure F.noRes
  | .op o es =>
    match o, es with
    | .not, [c] =>
      let r := an L d F c
      { r with tt := r.ff, ff := r.tt, lin := none }
    | o, es => opRes L d o es (anOps L d F es)
  | .list _ es => listRes L d es.length (anOps L d F es)
  | .index a i =>
    let ra := an L d F a
    indexRes d ra (an L (d + 1) (ra.post.push d) i)
  | .field e _ =>
    let r := an L d F e
    { r with post := r.post.noRes, tt := r.post.noRes, ff := r.post.noRes, lin := none }
  | .letIn x _ init body | .varIn x _ init body =>
    let r := an L d F init
    scopeRes x r (an L d (r.post.assignTo x) body)
  | .assign ⟨x, ps⟩ v =>
    match ps with
    | [] =>
      let r := an L d F v
      { Res.pure (r.post.assignTo x) with brk := r.brk, cont := r.cont, ok := r.ok }
    | [.index i] =>
      let ri := an L d F i
      storeRes d ri (an L (d + 1) (ri.post.push d) v)
    | ps => Res.after F (x :: (pathWrites ps ++ v.writes)) (okPath L d ps && (an L d .top v).ok)
  | .seq a b =>
    let ra := an L d F a
    seqRes ra (an L d ra.post.noRes b)
  | .if c _ a b =>
    let rc := an L d F c
    ifRes rc (an L d rc.tt.noRes a) (an L d rc.ff.noRes b)
  | .break => Res.leaves .bot .bot true |> fun r => { r with brk := F.noRes }
  | .continue => Res.leaves .bot .bot true |> fun r => { r with cont := F.noRes }
  | .return e | .raise e =>
    let r := an L d F e
    Res.leaves r.brk r.cont r.ok
  | .form f m =>
    match f, m with
    | .proved ks, .op o es =>
      let os := anOps L d F es
      let r := opRes L d o es os
      { r with ok := r.ok && ks.all (verifyOp o d os.lins os.post.noRes) }
    | .proved ks, .index a i =>
      let ra := an L d F a
      let ri := an L (d + 1) (ra.post.push d) i
      let r := indexRes d ra ri
      { r with ok := r.ok && ks.all (fun k => k == .bounds && indexProved a d ri) }
    | .proved ks, .assign ⟨x, [.index i]⟩ v =>
      let ri := an L d F i
      let rv := an L (d + 1) (ri.post.push d) v
      let r := storeRes d ri rv
      { r with ok := r.ok && ks.all (fun k => k == .bounds && rv.post.indexOk (.opnd d) (.len x)) }
    | .proved _, m => { an L d F m with ok := false }
    | _, m => an L d F m
  | .record _ _ fs => Res.after F (fieldsWrites fs) (okFields L d fs)
  | .variant _ _ _ es | .view es => Res.after F (exprsWrites es) (okExprs L d es)
  | .call f args _ => Res.after F (f.writes ++ argsWrites args) ((an L d .top f).ok && okArgs L d args)
  | .match e _ arms => Res.after F (e.writes ++ armsWrites arms) ((an L d .top e).ok && okArms L d arms)
  | .for x _ e body =>
    let re := an L d F e
    let lo := if e.isRange then re.lo.filter (·.1.steady x body.writes body.resizes true) else none
    let hi := if e.isExclusiveRange then re.hi.filter (·.1.steady x body.writes body.resizes false)
      else none
    let I := (loopHead (fun C => let rb := an L d (C.forRange x lo hi) body
      (rb.post.noRes.join rb.cont).unbind x) 3 (re.post.noRes.unbind x).close).unbind x
    forRes x re.post.noRes I re (an L d (I.forRange x lo hi) body)
      (Res.after F (e.writes ++ body.writes) ((an L d .top e).ok && (an L d .top body).ok))
  | .while c body =>
    let I := loopHead (fun C => let rc := an L d C c
      let rb := an L d rc.tt.noRes body
      rb.post.noRes.join rb.cont) 3 F.noRes.close
    let rc := an L d I c
    whileRes F I rc (an L d rc.tt.noRes body)
      (Res.after F (c.writes ++ body.writes) ((an L d .top c).ok && (an L d .top body).ok))
  | .loop body =>
    let I := loopHead (fun C => let rb := an L d C body; rb.post.noRes.join rb.cont) 3 F.noRes.close
    loopRes F I (an L d I body) (Res.after F body.writes ((an L d .top body).ok))
  | .try e => Res.after F e.writes ((an L d .top e).ok)
  | .tryCatch e _ _ h _ => Res.after F (e.writes ++ h.writes) ((an L d .top e).ok && (an L d .top h).ok)
  | .perform _ e => Res.after F e.writes ((an L d .top e).ok)
  | .withH _ _ h b => Res.after F (h.writes ++ b.writes) ((an L d .top h).ok && (an L d .top b).ok)
  | .held _ hs b => Res.after F (exprsWrites hs ++ b.writes) (okExprs L d hs && (an L d .top b).ok)

/-- Operands evaluated one after another, each value pushed before the next is evaluated. -/
def anOps (L : Bool) (d : Nat) (F : Facts) : List Expr → Ops
  | [] => { post := F, brk := .bot, cont := .bot, lins := [], ok := true }
  | e :: es =>
    let r := an L d F e
    let os := anOps L (d + 1) (r.post.push d) es
    { post := os.post, brk := r.brk.join (os.brk.within d), cont := r.cont.join (os.cont.within d),
      lins := r.lin :: os.lins, ok := r.ok && os.ok }

def okExprs (L : Bool) (d : Nat) : List Expr → Bool
  | [] => true
  | e :: es => (an L d .top e).ok && okExprs L d es

def okFields (L : Bool) (d : Nat) : List (Name × Expr) → Bool
  | [] => true
  | (_, e) :: fs => (an L d .top e).ok && okFields L d fs

def okPath (L : Bool) (d : Nat) : List Projection → Bool
  | [] => true
  | .field _ :: ps => okPath L d ps
  | .index i :: ps => (an L d .top i).ok && okPath L d ps

def okArgs (L : Bool) (d : Nat) : List Arg → Bool
  | [] => true
  | .value e :: args => (an L d .top e).ok && okArgs L d args
  | .inout ⟨_, ps⟩ :: args => okPath L d ps && okArgs L d args

def okArms (L : Bool) (d : Nat) : List Arm → Bool
  | [] => true
  | ⟨_, _, guard, body⟩ :: arms => okGuard L d guard && (an L d .top body).ok && okArms L d arms

def okGuard (L : Bool) (d : Nat) : Option Expr → Bool
  | none => true
  | some g => (an L d .top g).ok

end

/-- Whether every mark in `e` is proved from no fact. -/
def okIn (L : Bool) (d : Nat) (e : Expr) : Bool := (an L d .top e).ok

/-- Whether the analysis proves every mark of a body, analysed on its own from no fact
(facts.verification), keeping only bounds when the body is large (`Expr.large`): the body of a
function, of a closure literal or of a handler's operation, or `main`. -/
def Expr.verified (e : Expr) : Bool := (an e.large 0 .top e).ok

end Stilt
