import Stilt.Windows.Guards.Call

/-!
# Runs of several expressions

The steps of `Stilt.Semantics` that run expressions through `run`: lists, fields, the
indexes of a place, a call's arguments, the arms of a `match`, an assignment and a `for`
loop. Each keeps the guarded regions when each expression it runs does, under the reads of
its own scope; the indexes of a place give a path that resolves it, and a call's arguments
the places they name, which `Stilt.Windows.Guards.Eval` needs to show that a write misses
the regions.
-/

namespace Stilt.Eval.Guards

open InPlace

variable {G : List Path} {R R' : List Shape} {run : Expr → Eval (State × World) Value}

/-- With no region, the reads don't matter. -/
theorem nil_any {α : Type} {P : α → Prop} {m : Eval (State × World) α}
    (h : Eval.Guards [] R P m) : Eval.Guards [] R' P m :=
  fun s hv _ => h s hv (regions_nil _ _)

theorem list : ∀ es : List Expr, (∀ e ∈ es, Eval.Guards G R (fun _ => True) (run e)) →
    Eval.Guards G R (fun _ => True) (Eval.list run es)
  | [], _ => pure trivial
  | e :: es, h =>
    bind (h e List.mem_cons_self) fun _ _ =>
      bind (list es fun e' he' => h e' (List.mem_cons_of_mem _ he')) fun _ _ => pure trivial

theorem fields : ∀ fs : List (Name × Expr), (∀ fe ∈ fs, Eval.Guards G R (fun _ => True) (run fe.2)) →
    Eval.Guards G R (fun _ => True) (Eval.fields run fs)
  | [], _ => pure trivial
  | (f, e) :: fs, h =>
    bind (h (f, e) List.mem_cons_self) fun _ _ =>
      bind (fields fs fun fe hfe => h fe (List.mem_cons_of_mem _ hfe)) fun _ _ => pure trivial

/-- Evaluating the indexes of a place gives a path that resolves it. -/
theorem path : ∀ ps : List Projection,
    (∀ i, Projection.index i ∈ ps → Eval.Guards G R (fun _ => True) (run i)) →
    Eval.Guards G R (fun p : Path => p.Resolves ps) (Eval.path run ps)
  | [], _ => pure trivial
  | .field _ :: ps, h =>
    bind (path ps fun i hi => h i (List.mem_cons_of_mem _ hi)) fun _ hp => pure ⟨rfl, hp⟩
  | .index i :: ps, h =>
    bind (bind (h i List.mem_cons_self) fun _ _ => asInt) fun _ _ =>
      bind (path ps fun j hj => h j (List.mem_cons_of_mem _ hj)) fun _ hp => pure hp

/-- What each argument of a call must keep: a value argument's expression, and an `inout`
argument's indexes. -/
def ArgsKeep (G : List Path) (R : List Shape) (run : Expr → Eval (State × World) Value) :
    List Arg → Prop
  | [] => True
  | .value e :: as => Eval.Guards G R (fun _ => True) (run e) ∧ ArgsKeep G R run as
  | .inout ⟨_, ps⟩ :: as =>
    (∀ i, Projection.index i ∈ ps → Eval.Guards G R (fun _ => True) (run i)) ∧ ArgsKeep G R run as

/-- Evaluating a call's arguments gives the places the arguments name. -/
theorem args : ∀ as : List Arg, ArgsKeep G R run as →
    Eval.Guards G R (fun passed => Sim.ArgsResolved as passed) (Eval.args run as)
  | [], _ => pure trivial
  | .value e :: as, ⟨he, has⟩ =>
    bind he fun v _ => bind (args as has) fun _ hps => pure (Sim.resolved_ofArg e v hps)
  | .inout ⟨_, ps⟩ :: as, ⟨hps, has⟩ =>
    bind (path ps hps) fun _ hp => bind (args as has) fun _ hq => pure ⟨rfl, hp, hq⟩

/-- A `match` runs the arm it selects, whose reads hide the shapes rooted at its binders. -/
theorem select {arms : List Arm}
    (h : ∀ arm ∈ arms, Eval.Guards G (arm.binders.foldl hide R) (fun _ => True) (run arm.body))
    (v : Value) : Eval.Guards G R (fun _ => True) (Eval.select InPlace.memory run arms v) := by
  unfold Eval.select
  cases hsel : selectArm arms v with
  | none => exact fail _
  | some au =>
    obtain ⟨arm, us⟩ := au
    have hmem := (selectArm_mem hsel).1
    dsimp only
    by_cases hlen : arm.binders.length = us.length
    · simp only [hlen, ↓reduceIte]
      refine withVars _ ?_
      rw [List.map_fst_zip (Nat.le_of_eq hlen)]
      exact h arm hmem
    · simp only [hlen, ↓reduceIte]
      exact fail _

/-- An assignment keeps the regions when the place it writes, whatever its indexes, avoids
them. -/
theorem assign (x : Name) {ps : List Projection} {value : Expr}
    (hps : ∀ i, Projection.index i ∈ ps → Eval.Guards G R (fun _ => True) (run i))
    (hv : Eval.Guards G R (fun _ => True) (run value))
    (hw : ∀ p : Path, p.Resolves ps → ∀ (s : State) r, Regions G R s → s.env.lookup x = some r →
      Avoids G (r.toPath ++ p)) :
    Eval.Guards G R (fun _ => True) (Eval.assign InPlace.memory run x ps value) :=
  bind (path ps hps) fun p hp =>
    bind hv fun _ _ => bind (update x p _ (hw p hp)) fun _ _ => pure trivial

/-- A `for` loop, whose body's reads hide the shapes rooted at its variable. -/
theorem loop (x : Name) {e body : Expr} (he : Eval.Guards G R (fun _ => True) (run e))
    (hb : Eval.Guards G R' (fun _ => True) (run body)) (hR : ∀ t ∈ hide R x, t ∈ R') :
    Eval.Guards G R (fun _ => True) (Eval.loop InPlace.memory run x e body) :=
  bind (bind he fun _ _ => asList) fun vs _ =>
    bind (forEach (fun v => withVar x v (turn hb) hR) vs) fun _ _ => pure trivial

/-- An index into a value, the index read in its turn. -/
theorem index {e i : Expr} (he : Eval.Guards G R (fun _ => True) (run e))
    (hi : Eval.Guards G R (fun _ => True) (run i)) :
    Eval.Guards G R (fun _ => True) (do
      let v ← run e
      let k ← run i >>= Eval.asInt
      Eval.ofExcept (v.get [.index k])) :=
  bind he fun _ _ => bind (bind hi fun _ _ => asInt) fun _ _ => ofExcept _ fun _ _ => trivial

/-- A `while` loop, its next turns run as the loop itself. -/
theorem whileLoop {c body : Expr} (hc : Eval.Guards G R (fun _ => True) (run c))
    (hb : Eval.Guards G R (fun _ => True) (run body))
    (hl : Eval.Guards G R (fun _ => True) (run (.while c body))) :
    Eval.Guards G R (fun _ => True) (do
      if ← run c >>= Eval.asBool then
        if ← Eval.turn (run body) then run (.while c body) else Pure.pure .unit
      else Pure.pure .unit) :=
  bind (bind hc fun _ _ => asBool) fun v _ =>
    ite v (bind (turn hb) fun g _ => ite g hl (pure trivial)) (pure trivial)

/-- A `loop`, its next turns run as the loop itself. -/
theorem loopForever {body : Expr} (hb : Eval.Guards G R (fun _ => True) (run body))
    (hl : Eval.Guards G R (fun _ => True) (run (.loop body))) :
    Eval.Guards G R (fun _ => True) (do
      if ← Eval.turn (run body) then run (.loop body) else Pure.pure .unit) :=
  bind (turn hb) fun g _ => ite g hl (pure trivial)

end Stilt.Eval.Guards
