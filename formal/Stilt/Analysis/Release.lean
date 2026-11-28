import Stilt.Analysis.Analyze

/-!
# Release builds

A release build drops the checks that verification proves (facts.verification): the run of
`evalR` is `eval`'s, but where an operation marked `Form.proved ks` would panic with a kind of
`ks`, in a body every mark of which the analysis proves (`Expr.verified`), it gets stuck
instead, as code whose check is gone does what no run defines. A body that the analysis
doesn't prove whole keeps every check. `Stilt.Analysis.Agree` proves that the two runs are one:
no check that a release build drops ever fails.
-/

namespace Stilt

namespace Eval

variable {σ : Type}

/-- A fault with the panics of the kinds `ks` turned into `stuck`: what a check that is gone
leaves. -/
def dropped {α : Type} (ks : List PanicKind) : Except Fault α → Except Fault α
  | .error (.panic k) => if k ∈ ks then .error .stuck else .error (.panic k)
  | x => x

/-- A marked operation with the checks of `ks` dropped: an index read, an operation, or a store
through an index, its parts run by `run`, and anything else by `self`. -/
def proved (M : Memory σ) (ks : List PanicKind) (run self : Expr → Eval σ Value) :
    Expr → Eval σ Value
  | .index e i => do
    let v ← run e
    let k ← run i >>= asInt
    ofExcept (dropped ks (v.get [.index k]))
  | .op o es => do
    let vs ← list run es
    world M fun w => dropped ks (o.run vs w)
  | .assign ⟨x, ps⟩ value => do
    let p ← path run ps
    let v ← run value
    update fun s => dropped ks (M.write s x p v)
    pure .unit
  | m => self m

end Eval

section

variable {σ : Type} (D : Decls) (M : Memory σ)

/-- How a release build runs a body that a call runs: by `run`, dropping the checks its marks
name, when the analysis proves it whole, and keeping every check otherwise. -/
def evalBody (run : Expr → Eval σ Value) (n : Nat) (b : Expr) : Eval σ Value :=
  if b.verified then run b else eval D M n b

/-- A release build's run (facts.what-proofs-change): `eval`'s, but a marked operation in a body
the analysis proves whole drops the checks its mark names. A body a call runs is proved or not
on its own, where it is called. -/
def evalR : Nat → Expr → Eval σ Value
  | 0, _ => Eval.outOfFuel
  | n + 1, e =>
    let run := evalR n
    let body := evalBody D M (evalR n) n
    match e with
    | .form (.proved ks) m =>
      match n with
      | 0 => Eval.outOfFuel
      | k + 1 => Eval.proved M ks (evalR k) run m
    | .var x | .move x => Eval.inspect fun s => M.read s x []
    | .int k => pure (.int k)
    | .bool b => pure (.bool b)
    | .unit => pure .unit
    | .record R _ fields => do
      let written ← Eval.fields run fields
      Eval.declare D R written
    | .variant T _ C payload => do
      let vs ← Eval.list run payload
      pure (.variant T C vs)
    | .list _ es => do
      let vs ← Eval.list run es
      pure (.list vs)
    | .op o es => do
      let vs ← Eval.list run es
      Eval.world M (o.run vs)
    | .view es => do
      let vs ← Eval.list run es
      Eval.ofExcept (Op.view.apply vs)
    | .field e f => do
      let v ← run e
      Eval.ofExcept (v.get [.field f])
    | .index e i => do
      let v ← run e
      let k ← run i >>= Eval.asInt
      Eval.ofExcept (v.get [.index k])
    | .fnRef f types rows => pure (.function f types rows)
    | .method trait m τ => Eval.method D trait m τ
    | .closure ps result ρ b => do
      let captured ← Eval.inspect (M.capture · (Expr.captures ps b))
      pure (.closure captured ps result ρ b)
    | .call callee args _ => do
      let f ← run callee
      let passed ← Eval.args run args
      Eval.callAs D M body false f passed
    | .letIn x _ init b | .varIn x _ init b => do
      let v ← run init
      Eval.withInit M x init v (run b)
    | .assign ⟨x, projections⟩ value => Eval.assign M run x projections value
    | .seq a b => do
      let _ ← run a
      run b
    | .if c _ a b => do
      let v ← run c >>= Eval.asBool
      if v then run a else run b
    | .match e _ arms => do
      let v ← run e
      Eval.select M run arms v
    | .for x _ e b => Eval.loop M run x e b
    | .raise e => do
      let v ← run e
      Eval.throw v
    | .try e | .form _ e => run e
    | .tryCatch e _ x handler _ => Eval.handle (run e) fun err => Eval.withVar M x err (run handler)
    | .while c b => do
      if ← run c >>= Eval.asBool then
        if ← Eval.turn (run b) then run (.while c b) else pure .unit
      else pure .unit
    | .loop b => do
      if ← Eval.turn (run b) then run (.loop b) else pure .unit
    | .break => Eval.jump .brk
    | .continue => Eval.jump .cont
    | .return e => do
      let v ← run e
      Eval.jump (.ret v)
    | .perform op e => do
      let v ← run e
      Eval.perform M op v
    | .withH E c h b => do
      let hv ← run h
      Eval.letGo M (Eval.handleWith M E c hv (fun f v => Eval.callAs D M body c f [.value v]) (run b))
    | .held names handles b => do
      let hs ← Eval.list run handles
      Eval.held M (run b) (names.map Prod.fst) hs

end

/-- Runs `main` as a release build does, on an input: `main` proved whole drops the checks its
marks name, and every body a call runs too, when it is proved whole. -/
def Program.runRelease (p : Program) (fuel : Nat) (input : String := "") : Outcome Copy.State Value :=
  (if p.main.verified then evalR p.decls Copy.memory fuel p.main ([], World.start input)
    else eval p.decls Copy.memory fuel p.main ([], World.start input)).leaveBody

end Stilt
