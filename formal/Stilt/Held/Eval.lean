import Stilt.Held.Outcome

/-!
# Evaluation that keeps a cell held

Each part of the evaluator keeps a held cell held (`Eval.KeepsHeld`): reading and writing
variables, binding them and calling functions leave the world; an operation on the world
writes its output, reads its input or makes a cell; a performance's rest goes on in the
world it is resumed in; and a `when` holds only cells that no one holds, so it puts values
back in none that was held before it (shared.when-on-value-already-held).
-/

namespace Stilt

namespace Eval.KeepsHeld

variable {τ α β : Type} {k : Ty × Nat}

theorem pure (a : α) : Eval.KeepsHeld k (Pure.pure a : Eval (τ × World) α) := fun s hk =>
  ⟨World.Extends.refl s.2, hk⟩

theorem bind {m : Eval (τ × World) α} {f : α → Eval (τ × World) β} (hm : Eval.KeepsHeld k m)
    (hf : ∀ a, Eval.KeepsHeld k (f a)) : Eval.KeepsHeld k (m >>= f) := fun s hk =>
  Outcome.KeepsHeld.bind (fun a s' _ hk' => hf a s' hk') (hm s hk)

theorem fail (f : Fault) : Eval.KeepsHeld k (Eval.fail f : Eval (τ × World) α) := fun s hk =>
  Outcome.KeepsHeld.fault f (World.Extends.refl s.2) hk

theorem ofExcept (x : Except Fault α) : Eval.KeepsHeld k (Eval.ofExcept x : Eval (τ × World) α) := by
  intro s hk
  cases x with
  | ok a => exact ⟨World.Extends.refl s.2, hk⟩
  | error f => exact Outcome.KeepsHeld.fault f (World.Extends.refl s.2) hk

theorem inspect (f : τ × World → Except Fault α) : Eval.KeepsHeld k (Eval.inspect f) := fun s hk =>
  ofExcept (f s) s hk

theorem throw (e : Value) : Eval.KeepsHeld k (Eval.throw e : Eval (τ × World) α) := fun s hk =>
  ⟨World.Extends.refl s.2, hk⟩

theorem jump (j : Jump) : Eval.KeepsHeld k (Eval.jump j : Eval (τ × World) α) := fun s hk =>
  ⟨World.Extends.refl s.2, hk⟩

theorem handle {m : Eval (τ × World) α} {h : Value → Eval (τ × World) α} (hm : Eval.KeepsHeld k m)
    (hh : ∀ e, Eval.KeepsHeld k (h e)) : Eval.KeepsHeld k (Eval.handle m h) := fun s hk =>
  Outcome.KeepsHeld.handle (fun e s' _ hk' => hh e s' hk') (hm s hk)

theorem turn {m : Eval (τ × World) Value} (hm : Eval.KeepsHeld k m) :
    Eval.KeepsHeld k (Eval.turn m) := fun s hk => Outcome.KeepsHeld.turn (hm s hk)

theorem forEach {body : Value → Eval (τ × World) Bool} (hb : ∀ v, Eval.KeepsHeld k (body v)) :
    ∀ vs : List Value, Eval.KeepsHeld k (Eval.forEach body vs)
  | [] => pure ()
  | v :: vs => by
    unfold Eval.forEach
    refine bind (hb v) fun b => ?_
    cases b
    · exact pure ()
    · exact forEach hb vs

theorem ite (b : Bool) {m₁ m₂ : Eval (τ × World) α} (h₁ : Eval.KeepsHeld k m₁)
    (h₂ : Eval.KeepsHeld k m₂) : Eval.KeepsHeld k (if b then m₁ else m₂) := by
  cases b
  · exact h₂
  · exact h₁

theorem asInt (v : Value) : Eval.KeepsHeld k (Eval.asInt v : Eval (τ × World) Int) := by
  cases v <;> first | exact pure _ | exact fail _

theorem asBool (v : Value) : Eval.KeepsHeld k (Eval.asBool v : Eval (τ × World) Bool) := by
  cases v <;> first | exact pure _ | exact fail _

theorem asList (v : Value) : Eval.KeepsHeld k (Eval.asList v : Eval (τ × World) (List Value)) := by
  cases v <;> first | exact pure _ | exact fail _

variable (F : Frames τ)

theorem withVar (x : Name) (v : Value) {m : Eval (τ × World) α} (hm : Eval.KeepsHeld k m) :
    Eval.KeepsHeld k (Eval.withVar F.withWorld x v m) := fun ⟨fr, w⟩ hk =>
  Outcome.KeepsHeld.unbind F (hm (F.bind fr x v, w) hk)

theorem withInit (x : Name) (init : Expr) (v : Value) {m : Eval (τ × World) α}
    (hm : Eval.KeepsHeld k m) : Eval.KeepsHeld k (Eval.withInit F.withWorld x init v m) := by
  rintro ⟨fr, w⟩ hk
  unfold Eval.withInit Memory.bindInit
  cases init
  case move y => exact Outcome.KeepsHeld.unbind F (hm (F.bindMoved fr x y v, w) hk)
  all_goals exact Outcome.KeepsHeld.unbind F (hm (F.bind fr x v, w) hk)

theorem withVars {m : Eval (τ × World) α} (hm : Eval.KeepsHeld k m) :
    ∀ bs : List (Name × Value), Eval.KeepsHeld k (Eval.withVars F.withWorld bs m)
  | [] => hm
  | (x, v) :: bs => withVar F x v (withVars hm bs)

/-- An operation on the world keeps every cell in its place, and every held cell held. -/
theorem world {f : World → Except Fault (Value × World)}
    (hf : ∀ w v w', f w = .ok (v, w') → w.Extends w' ∧ (w.Held k → w'.Held k)) :
    Eval.KeepsHeld k (Eval.world F.withWorld f) := by
  rintro ⟨fr, w⟩ hk
  cases h : f w with
  | ok p =>
    rw [Eval.world_ok h]
    obtain ⟨he, hk'⟩ := hf w p.1 p.2 h
    exact ⟨he, hk' hk⟩
  | error e =>
    rw [Eval.world_error h]
    exact Outcome.KeepsHeld.fault e (World.Extends.refl w) hk

theorem run (o : Op) (vs : List Value) : Eval.KeepsHeld k (Eval.world F.withWorld (o.run vs)) :=
  world F fun _ _ _ h => ⟨(Op.run_held h).1, (Op.run_held h).2 k⟩

theorem update (x : Name) (p : Path) (v : Value) :
    Eval.KeepsHeld k (Eval.update fun s => F.withWorld.write s x p v) := by
  rintro ⟨fr, w⟩ hk
  unfold Eval.update
  dsimp only
  rw [Frames.withWorld_write]
  cases F.write fr x p v with
  | ok _ => exact ⟨World.Extends.refl w, hk⟩
  | error f => exact Outcome.KeepsHeld.fault f (World.Extends.refl w) hk

theorem perform (op : Operation) (v : Value) :
    Eval.KeepsHeld k (Eval.perform F.withWorld op v) := fun ⟨_, w⟩ hk =>
  ⟨World.Extends.refl w, hk, fun _ w' _ hk' => ⟨World.Extends.refl w', hk'⟩⟩

theorem invoke (captured : List (Name × Value)) (params : List Param) (passed : List Passed)
    {body : Eval (τ × World) Value} (hb : Eval.KeepsHeld k body) :
    Eval.KeepsHeld k (Eval.invoke F.withWorld captured params passed body) := by
  rintro ⟨fr, w⟩ hk
  unfold Eval.invoke
  cases bindArgs params passed with
  | none => trivial
  | some bound =>
    dsimp only
    rw [Frames.withWorld_enter]
    cases F.enter fr captured bound with
    | error f => exact Outcome.KeepsHeld.fault f (World.Extends.refl w) hk
    | ok callee => exact Outcome.KeepsHeld.leaveCall F bound _ (hb (callee, w) hk)

section Runs

variable {run : Expr → Eval (τ × World) Value} (h : ∀ e, Eval.KeepsHeld k (run e))
include h

theorem call (D : Decls) (f : Value) (passed : List Passed) :
    Eval.KeepsHeld k (Eval.call D F.withWorld run f passed) := by
  cases f with
  | closure captured params result ρ body => exact invoke F captured params passed (h _)
  | function name types rows =>
    unfold Eval.call
    dsimp only
    cases D.fn? name with
    | none => exact fail _
    | some d => exact invoke F [] d.params passed (h _)
  | _ => exact fail _

theorem callAs (D : Decls) (control : Bool) (f : Value) (passed : List Passed) :
    Eval.KeepsHeld k (Eval.callAs D F.withWorld run control f passed) := by
  unfold Eval.callAs
  split
  · exact fail _
  · exact call F h D f passed

omit F in
theorem list : ∀ es : List Expr, Eval.KeepsHeld k (Eval.list run es)
  | [] => pure _
  | e :: es => bind (h e) fun _ => bind (list es) fun _ => pure _

omit F in
theorem fields : ∀ fs : List (Name × Expr), Eval.KeepsHeld k (Eval.fields run fs)
  | [] => pure _
  | (_, e) :: fs => bind (h e) fun _ => bind (fields fs) fun _ => pure _

omit F in
theorem path : ∀ ps : List Projection, Eval.KeepsHeld k (Eval.path run ps)
  | [] => pure _
  | .field _ :: ps => bind (path ps) fun _ => pure _
  | .index i :: ps => bind (bind (h i) asInt) fun _ => bind (path ps) fun _ => pure _

omit F in
theorem args : ∀ as : List Arg, Eval.KeepsHeld k (Eval.args run as)
  | [] => pure _
  | .value e :: as => bind (h e) fun _ => bind (args as) fun _ => pure _
  | .inout ⟨_, ps⟩ :: as => bind (path h ps) fun _ => bind (args as) fun _ => pure _

theorem select (arms : List Arm) (v : Value) :
    Eval.KeepsHeld k (Eval.select F.withWorld run arms v) := by
  unfold Eval.select
  cases selectArm arms v with
  | none => exact fail _
  | some au =>
    dsimp only
    split
    · exact withVars F (h _) _
    · exact fail _

theorem assign (x : Name) (ps : List Projection) (value : Expr) :
    Eval.KeepsHeld k (Eval.assign F.withWorld run x ps value) :=
  bind (path h ps) fun p => bind (h value) fun v => bind (update F x p v) fun _ => pure _

theorem loop (x : Name) (e body : Expr) : Eval.KeepsHeld k (Eval.loop F.withWorld run x e body) :=
  bind (bind (h e) asList) fun vs =>
    bind (forEach (fun v => withVar F x v (turn (h body))) vs) fun _ => pure _

end Runs

omit F in
theorem declare (D : Decls) (R : Name) (written : List (Name × Value)) :
    Eval.KeepsHeld k (Eval.declare D R written : Eval (τ × World) Value) := by
  unfold Eval.declare
  split
  · split
    · exact pure _
    · exact fail _
  · exact fail _

omit F in
theorem method (D : Decls) (t m : Name) (ty : Ty) :
    Eval.KeepsHeld k (Eval.method D t m ty : Eval (τ × World) Value) := by
  unfold Eval.method
  split
  · split
    · exact pure _
    · exact fail _
  · exact fail _

/-- A `with` keeps a cell held when its block and its clauses do, and lets go of none held
when it started (handlers.with, shared.when). -/
theorem withH (effect : Name) (control : Bool) (handler : Value)
    {call : Value → Value → Eval (τ × World) Value} (hc : ∀ c v, Eval.KeepsHeld k (call c v))
    {m : Eval (τ × World) Value} (hm : Eval.KeepsHeld k m) :
    Eval.KeepsHeld k (Eval.letGo F.withWorld (Eval.handleWith F.withWorld effect control handler call m)) :=
  fun s hk => Outcome.KeepsHeld.letGo F hk (World.Extends.refl s.2)
    (Outcome.KeepsHeld.handleWith F (fun c v s' hk' => hc c v s' hk') (hm s hk))

end Eval.KeepsHeld

end Stilt
