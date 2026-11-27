import Stilt.Selection
import Stilt.Semantics

/-!
# The jumps code may end with

`Expr.exits loops rets e`: every `break` and `continue` of `e` is in a loop of its own or in a
closure literal's body, unless `loops`, and every `return` in a closure literal's body, unless
`rets`. Code that passes it ends with no other jump (`eval_exits`), in any model of memory: a
loop's turn takes in the `break`s and `continue`s of its body, and a call every jump of the body
it runs.
-/

namespace Stilt

mutual

/-- Whether `e` ends with a `break` or a `continue` only when `loops`, and with a `return` only
when `rets`. -/
def Expr.exits (loops rets : Bool) : Expr → Bool
  | .break | .continue => loops
  | .var _ | .move _ | .int _ | .bool _ | .unit | .fnRef _ _ _ | .method _ _ _
  | .closure _ _ _ _ => true
  | .record _ _ fields => fieldsExit loops rets fields
  | .variant _ _ _ es | .list _ es | .op _ es | .view es => exprsExit loops rets es
  | .field e _ | .raise e | .try e | .form _ e | .perform _ e => e.exits loops rets
  | .return e => rets && e.exits loops rets
  | .index a b | .seq a b | .letIn _ _ a b | .varIn _ _ a b | .tryCatch a _ _ b _
  | .withH _ _ a b => a.exits loops rets && b.exits loops rets
  | .call callee args _ => callee.exits loops rets && argsExit loops rets args
  | .assign ⟨_, path⟩ value => pathExits loops rets path && value.exits loops rets
  | .if c _ a b => c.exits loops rets && a.exits loops rets && b.exits loops rets
  | .match e _ arms => e.exits loops rets && armsExit loops rets arms
  | .for _ _ e body => e.exits loops rets && body.exits true rets
  | .while c body => c.exits loops rets && body.exits true rets
  | .loop body => body.exits true rets
  | .held _ hs body => exprsExit loops rets hs && body.exits loops rets

def exprsExit (loops rets : Bool) : List Expr → Bool
  | [] => true
  | e :: es => e.exits loops rets && exprsExit loops rets es

def fieldsExit (loops rets : Bool) : List (Name × Expr) → Bool
  | [] => true
  | (_, e) :: fields => e.exits loops rets && fieldsExit loops rets fields

def argsExit (loops rets : Bool) : List Arg → Bool
  | [] => true
  | .value e :: args => e.exits loops rets && argsExit loops rets args
  | .inout ⟨_, path⟩ :: args => pathExits loops rets path && argsExit loops rets args

def pathExits (loops rets : Bool) : List Projection → Bool
  | [] => true
  | .field _ :: path => pathExits loops rets path
  | .index i :: path => i.exits loops rets && pathExits loops rets path

def armsExit (loops rets : Bool) : List Arm → Bool
  | [] => true
  | ⟨_, _, guard, body⟩ :: arms =>
    guardExits loops rets guard && body.exits loops rets && armsExit loops rets arms

def guardExits (loops rets : Bool) : Option Expr → Bool
  | none => true
  | some g => g.exits loops rets

end

/-- A jump that `loops` and `rets` allow. -/
def Jump.Allowed (loops rets : Bool) : Jump → Prop
  | .brk | .cont => loops = true
  | .ret _ => rets = true

/-- An outcome that is no jump but one that `loops` and `rets` allow, nor a performance whose
rest, resumed with any value, may end with one. -/
def Outcome.Exits {σ α : Type} (loops rets : Bool) : Outcome σ α → Prop
  | .jumped j _ => j.Allowed loops rets
  | .performed _ _ _ k => ∀ w x, Outcome.Exits loops rets (k w x)
  | _ => True

/-- `m` ends with no jump but those `loops` and `rets` allow, a performance's rest included. -/
def Eval.Exits {σ α : Type} (loops rets : Bool) (m : Eval σ α) : Prop :=
  ∀ s, (m s).Exits loops rets

namespace Outcome.Exits

variable {σ α β : Type} {loops rets : Bool}

theorem fault (f : Fault) (s : σ) : (Outcome.fault f s : Outcome σ α).Exits loops rets := by
  cases f <;> trivial

theorem bind {f : α → σ → Outcome σ β} (hf : ∀ a s, (f a s).Exits loops rets) :
    ∀ {o : Outcome σ α}, o.Exits loops rets → (o.bind f).Exits loops rets
  | .done a s, _ => hf a s
  | .performed _ _ _ _, h => fun w x => bind hf (h w x)
  | .jumped _ _, h => h
  | .raised _ _, h | .panicked _ _, h | .outOfFuel, h | .stuck, h => h

theorem handle {h : Value → σ → Outcome σ α} (hh : ∀ e s, (h e s).Exits loops rets) :
    ∀ {o : Outcome σ α}, o.Exits loops rets → (o.handle h).Exits loops rets
  | .raised e s, _ => hh e s
  | .performed _ _ _ _, h' => fun w x => handle hh (h' w x)
  | .jumped _ _, h' => h'
  | .done _ _, h' | .panicked _ _, h' | .outOfFuel, h' | .stuck, h' => h'

/-- A loop's turn takes in its body's `break`s and `continue`s. -/
theorem turn : ∀ {o : Outcome σ Value}, o.Exits true rets → o.turn.Exits loops rets
  | .performed _ _ _ _, h => fun w x => turn (h w x)
  | .jumped (.ret _) _, h => h
  | .jumped .cont _, _ | .jumped .brk _, _ | .done _ _, _ | .raised _ _, _ | .panicked _ _, _
  | .outOfFuel, _ | .stuck, _ => trivial

theorem unbind (M : Memory σ) : ∀ {o : Outcome σ α}, o.Exits loops rets → (o.unbind M).Exits loops rets
  | .performed _ _ _ _, h => fun w x => unbind M (h w x)
  | .jumped _ _, h => h
  | .done _ _, h | .raised _ _, h | .panicked _ _, h | .outOfFuel, h | .stuck, h => h

/-- A call takes in every jump of its body. -/
theorem leaveCall (M : Memory σ) (bound : List (Name × Passed)) (s : σ) :
    ∀ o : Outcome σ Value, (o.leaveCall M bound s).Exits loops rets
  | .done _ s' | .raised _ s' | .jumped (.ret _) s' | .panicked _ s' => by
    simp only [Outcome.leaveCall]
    split <;> first | trivial | exact fault _ _
  | .performed _ _ s' k => by
    simp only [Outcome.leaveCall]
    split
    · exact fun w x => leaveCall M bound s (k w x)
    · exact fault _ _
  | .jumped .brk _ | .jumped .cont _ | .outOfFuel | .stuck => trivial

theorem lift (M : Memory σ) (s : σ) : ∀ {o : Outcome σ α}, o.Exits loops rets → (o.lift M s).Exits loops rets
  | .performed _ _ _ _, h => fun w x => lift M s (h w x)
  | .jumped _ _, h => h
  | .done _ _, h | .raised _ _, h | .panicked _ _, h | .outOfFuel, h | .stuck, h => h

theorem runBody (M : Memory σ) {resume : Value → World → Outcome σ Value}
    (hr : ∀ u x, (resume u x).Exits loops rets) :
    ∀ {o : Outcome σ Value}, o.Exits loops rets → (o.runBody M resume).Exits loops rets
  | .performed op u s k, h => by
    unfold Outcome.runBody
    split
    · exact bind (fun r s' => lift M s' (runBody M hr (h r _))) (hr u _)
    · exact fun w x => runBody M hr (h w x)
  | .jumped _ _, h => h
  | .done _ _, h | .raised _ _, h | .panicked _ _, h | .outOfFuel, h | .stuck, h => h

/-- A `with` whose block and clauses' calls end with no jump but those allowed ends with none. -/
theorem handleWith (M : Memory σ) {effect : Name} {control : Bool} {handler : Value}
    {call : Value → Value → σ → Outcome σ Value} (hcall : ∀ c v s, (call c v s).Exits loops rets) :
    ∀ {o : Outcome σ Value}, o.Exits loops rets →
      (o.handleWith M effect control handler call).Exits loops rets
  | .performed op v s k, h => by
    unfold Outcome.handleWith
    split
    · split
      · trivial
      · split
        · exact runBody M (fun u x => handleWith M hcall (h u x)) (hcall _ v s)
        · exact bind (fun w _ => handleWith M hcall (h w _)) (hcall _ v s)
    · exact fun w x => handleWith M hcall (h w x)
  | .jumped _ _, h => h
  | .done _ _, h | .raised _ _, h | .panicked _ _, h | .outOfFuel, h | .stuck, h => h

theorem after {f : σ → Except Fault σ} {s : σ} {o : σ → Outcome σ α}
    (ho : ∀ s', (o s').Exits loops rets) : (Outcome.after f s o).Exits loops rets := by
  unfold Outcome.after
  split
  · exact ho _
  · exact fault _ _

theorem release (M : Memory σ) (cells : List (Name × Ty × Nat)) :
    ∀ {o : Outcome σ α}, o.Exits loops rets → (o.release M cells).Exits loops rets
  | .performed _ _ _ _, h => after fun _ w x => release M cells (h w x)
  | .jumped _ _, h => after fun _ => h
  | .done _ _, _ | .raised _ _, _ | .panicked _ _, _ => after fun _ => trivial
  | .outOfFuel, h | .stuck, h => h

theorem letGo (M : Memory σ) (before : World) :
    ∀ {o : Outcome σ α}, o.Exits loops rets → (o.letGo M before).Exits loops rets
  | .performed _ _ _ _, h => fun w x => letGo M before (h w x)
  | .jumped _ _, h => h
  | .done _ _, h | .raised _ _, h | .panicked _ _, h | .outOfFuel, h | .stuck, h => h

end Outcome.Exits

namespace Eval.Exits

variable {σ α β : Type} {loops rets : Bool}

theorem pure (a : α) : Eval.Exits loops rets (Pure.pure a : Eval σ α) := fun _ => trivial

theorem fail (f : Fault) : Eval.Exits loops rets (Eval.fail f : Eval σ α) := fun s =>
  Outcome.Exits.fault f s

theorem ofExcept (x : Except Fault α) : Eval.Exits loops rets (Eval.ofExcept x : Eval σ α) := by
  intro s
  cases x with
  | ok a => trivial
  | error f => exact Outcome.Exits.fault f s

theorem inspect (f : σ → Except Fault α) : Eval.Exits loops rets (Eval.inspect f) := fun s =>
  ofExcept (f s) s

theorem world (M : Memory σ) (f : World → Except Fault (Value × World)) :
    Eval.Exits loops rets (Eval.world M f) := by
  intro s
  unfold Eval.world
  split
  · trivial
  · exact Outcome.Exits.fault _ s

theorem update (f : σ → Except Fault σ) : Eval.Exits loops rets (Eval.update f) := by
  intro s
  unfold Eval.update
  cases f s
  · exact Outcome.Exits.fault _ s
  · trivial

theorem throw (e : Value) : Eval.Exits loops rets (Eval.throw e : Eval σ α) := fun _ => trivial

theorem jump {j : Jump} (hj : j.Allowed loops rets) : Eval.Exits loops rets (Eval.jump j : Eval σ α) :=
  fun _ => hj

theorem bind {m : Eval σ α} {f : α → Eval σ β} (hm : Eval.Exits loops rets m)
    (hf : ∀ a, Eval.Exits loops rets (f a)) : Eval.Exits loops rets (m >>= f) := fun s =>
  Outcome.Exits.bind (fun a s' => hf a s') (hm s)

theorem ite (b : Bool) {m₁ m₂ : Eval σ α} (h₁ : Eval.Exits loops rets m₁)
    (h₂ : Eval.Exits loops rets m₂) : Eval.Exits loops rets (if b then m₁ else m₂) := by
  cases b
  · exact h₂
  · exact h₁

theorem handle {m : Eval σ α} {h : Value → Eval σ α} (hm : Eval.Exits loops rets m)
    (hh : ∀ e, Eval.Exits loops rets (h e)) : Eval.Exits loops rets (Eval.handle m h) := fun s =>
  Outcome.Exits.handle (fun e s' => hh e s') (hm s)

theorem turn {m : Eval σ Value} (hm : Eval.Exits true rets m) :
    Eval.Exits loops rets (Eval.turn m) := fun s => Outcome.Exits.turn (hm s)

theorem forEach {body : Value → Eval σ Bool} (hb : ∀ v, Eval.Exits loops rets (body v)) :
    ∀ vs, Eval.Exits loops rets (Eval.forEach body vs)
  | [] => pure ()
  | v :: vs => by
    unfold Eval.forEach
    exact bind (hb v) fun b => ite b (forEach hb vs) (pure ())

theorem asBool (v : Value) : Eval.Exits loops rets (Eval.asBool v : Eval σ Bool) := by
  cases v <;> first | exact pure _ | exact fail _

theorem asInt (v : Value) : Eval.Exits loops rets (Eval.asInt v : Eval σ Int) := by
  cases v <;> first | exact pure _ | exact fail _

theorem asList (v : Value) : Eval.Exits loops rets (Eval.asList v : Eval σ (List Value)) := by
  cases v <;> first | exact pure _ | exact fail _

section

variable (M : Memory σ)

theorem withVar (x : Name) (v : Value) {m : Eval σ α} (hm : Eval.Exits loops rets m) :
    Eval.Exits loops rets (Eval.withVar M x v m) := fun s =>
  Outcome.Exits.unbind M (hm (M.bind s x v))

theorem withInit (x : Name) (init : Expr) (v : Value) {m : Eval σ α}
    (hm : Eval.Exits loops rets m) : Eval.Exits loops rets (Eval.withInit M x init v m) := fun s =>
  Outcome.Exits.unbind M (hm (M.bindInit s x init v))

theorem withVars {m : Eval σ α} (hm : Eval.Exits loops rets m) :
    ∀ bs : List (Name × Value), Eval.Exits loops rets (Eval.withVars M bs m)
  | [] => hm
  | (x, v) :: bs => withVar M x v (withVars hm bs)

theorem invoke (captured : List (Name × Value)) (params : List Param) (passed : List Passed)
    (body : Eval σ Value) : Eval.Exits loops rets (Eval.invoke M captured params passed body) := by
  intro s
  unfold Eval.invoke
  split
  · trivial
  · split
    · exact Outcome.Exits.fault _ s
    · exact Outcome.Exits.leaveCall M _ s _

theorem call (D : Decls) (run : Expr → Eval σ Value) (f : Value) (passed : List Passed) :
    Eval.Exits loops rets (Eval.call D M run f passed) := by
  unfold Eval.call
  split
  · exact invoke M _ _ _ _
  · split
    · exact invoke M _ _ _ _
    · exact fail _
  · exact fail _

theorem callAs (D : Decls) (run : Expr → Eval σ Value) (control : Bool) (f : Value)
    (passed : List Passed) : Eval.Exits loops rets (Eval.callAs D M run control f passed) := by
  unfold Eval.callAs
  split
  · exact fail _
  · exact call M D run f passed

end

/-- Running code that passes `Expr.exits` ends with no other jump. -/
def ExitsRun (run : Expr → Eval σ Value) : Prop :=
  ∀ loops rets e, e.exits loops rets = true → Eval.Exits loops rets (run e)

section Runs

variable (M : Memory σ) {run : Expr → Eval σ Value} (h : ExitsRun run)
include h

theorem list : ∀ es : List Expr, exprsExit loops rets es = true →
    Eval.Exits loops rets (Eval.list run es)
  | [], _ => pure _
  | e :: es, hc => by
    simp only [exprsExit, Bool.and_eq_true] at hc
    exact bind (h _ _ e hc.1) fun _ => bind (list es hc.2) fun _ => pure _

theorem fields : ∀ fs : List (Name × Expr), fieldsExit loops rets fs = true →
    Eval.Exits loops rets (Eval.fields run fs)
  | [], _ => pure _
  | (_, e) :: fs, hc => by
    simp only [fieldsExit, Bool.and_eq_true] at hc
    exact bind (h _ _ e hc.1) fun _ => bind (fields fs hc.2) fun _ => pure _

theorem path : ∀ ps : List Projection, pathExits loops rets ps = true →
    Eval.Exits loops rets (Eval.path run ps)
  | [], _ => pure _
  | .field _ :: ps, hc => by
    simp only [pathExits] at hc
    exact bind (path ps hc) fun _ => pure _
  | .index i :: ps, hc => by
    simp only [pathExits, Bool.and_eq_true] at hc
    exact bind (bind (h _ _ i hc.1) fun v => asInt v) fun _ => bind (path ps hc.2) fun _ => pure _

theorem args : ∀ as : List Arg, argsExit loops rets as = true → Eval.Exits loops rets (Eval.args run as)
  | [], _ => pure _
  | .value e :: as, hc => by
    simp only [argsExit, Bool.and_eq_true] at hc
    exact bind (h _ _ e hc.1) fun _ => bind (args as hc.2) fun _ => pure _
  | .inout ⟨_, ps⟩ :: as, hc => by
    simp only [argsExit, Bool.and_eq_true] at hc
    exact bind (path h ps hc.1) fun _ => bind (args as hc.2) fun _ => pure _

omit h in
theorem arms_mem : ∀ {arms : List Arm} {arm : Arm}, armsExit loops rets arms = true → arm ∈ arms →
    arm.body.exits loops rets = true ∧ ∀ g, arm.guard = some g → g.exits loops rets = true
  | ⟨_, _, _, _⟩ :: _, _, hc, hm => by
    simp only [armsExit, Bool.and_eq_true] at hc
    rcases List.mem_cons.1 hm with rfl | hm
    · exact ⟨hc.1.2, fun g hg => by subst hg; exact hc.1.1⟩
    · exact arms_mem hc.2 hm

theorem select {arms : List Arm} (hc : armsExit loops rets arms = true) (v : Value) :
    Eval.Exits loops rets (Eval.select M run arms v) :=
  Eval.select_of (Eval.Exits loops rets) (.inl (fail _)) (.inl (fail _))
    (fun _ ha _ _ _ _ => withVars M (h _ _ _ (arms_mem hc ha).1) _) fun _ ha g hg _ _ _ _ hm =>
      bind (withVars M (bind (h _ _ g ((arms_mem hc ha).2 g hg)) fun v => asBool v) _) fun b =>
        ite b (withVars M (h _ _ _ (arms_mem hc ha).1) _) hm

theorem assign (x : Name) {ps : List Projection} (hp : pathExits loops rets ps = true) {value : Expr}
    (hv : value.exits loops rets = true) : Eval.Exits loops rets (Eval.assign M run x ps value) :=
  bind (path h ps hp) fun _ => bind (h _ _ value hv) fun _ => bind (update _) fun _ => pure _

theorem loop (x : Name) {e body : Expr} (he : e.exits loops rets = true)
    (hb : body.exits true rets = true) : Eval.Exits loops rets (Eval.loop M run x e body) :=
  bind (bind (h _ _ e he) fun v => asList v) fun vs =>
    bind (forEach (fun v => withVar M x v (turn (h _ _ body hb))) vs) fun _ => pure _

end Runs

end Eval.Exits

open Eval.Exits in
/-- Evaluating code that passes `Expr.exits loops rets`, with any fuel, ends with no jump but
those `loops` and `rets` allow, a performance's rest included. -/
theorem eval_exits {σ : Type} (D : Decls) (M : Memory σ) : ∀ n, ExitsRun (eval D M n)
  | 0, _, _, _, _ => fun _ => trivial
  | n + 1, loops, rets, e, hc => by
    have ih := eval_exits D M n
    cases e <;> try simp only [Expr.exits, Bool.and_eq_true] at hc
    case var x => exact inspect _
    case move x => exact inspect _
    case int k | bool b | unit => exact pure _
    case record R _ fs =>
      exact bind (fields ih fs hc) fun _ => by
        show Eval.Exits loops rets (Eval.declare D R _)
        unfold Eval.declare
        split
        · split
          · exact pure _
          · exact fail _
        · exact fail _
    case variant T _ C es => exact bind (list ih es hc) fun _ => pure _
    case list τ es => exact bind (list ih es hc) fun _ => pure _
    case op o es => exact bind (list ih es hc) fun _ => world M _
    case view es => exact bind (list ih es hc) fun _ => ofExcept _
    case field e f => exact bind (ih _ _ e hc) fun _ => ofExcept _
    case index e i =>
      exact bind (ih _ _ e hc.1) fun _ => bind (bind (ih _ _ i hc.2) fun v => asInt v) fun _ => ofExcept _
    case fnRef f types rows => exact pure _
    case method t m τ =>
      show Eval.Exits loops rets (Eval.method D t m τ)
      unfold Eval.method
      split
      · split
        · exact pure _
        · exact fail _
      · exact fail _
    case closure ps result ρ body => exact bind (inspect _) fun _ => pure _
    case call callee as _ =>
      exact bind (ih _ _ callee hc.1) fun f => bind (args ih as hc.2) fun ps => callAs M D _ false f ps
    case letIn x τ init body => exact bind (ih _ _ init hc.1) fun v => withInit M x init v (ih _ _ body hc.2)
    case varIn x τ init body => exact bind (ih _ _ init hc.1) fun v => withInit M x init v (ih _ _ body hc.2)
    case assign p value =>
      obtain ⟨x, ps⟩ := p
      simp only [Expr.exits, Bool.and_eq_true] at hc
      exact assign M ih x hc.1 hc.2
    case seq a b => exact bind (ih _ _ a hc.1) fun _ => ih _ _ b hc.2
    case «if» c τ a b =>
      exact bind (bind (ih _ _ c hc.1.1) fun v => asBool v) fun v => ite v (ih _ _ a hc.1.2) (ih _ _ b hc.2)
    case «match» e τ arms => exact bind (ih _ _ e hc.1) fun v => select M ih hc.2 v
    case «for» x τ e body => exact loop M ih x hc.1 hc.2
    case raise e => exact bind (ih _ _ e hc) fun v => throw v
    case «try» e => exact ih _ _ e hc
    case form _ e => exact ih _ _ e hc
    case tryCatch e E x h τ => exact handle (ih _ _ e hc.1) fun err => withVar M x err (ih _ _ h hc.2)
    case «while» c body =>
      have hl := ih loops rets (.while c body) (by simp only [Expr.exits, hc.1, hc.2, Bool.and_self])
      exact bind (bind (ih _ _ c hc.1) fun v => asBool v) fun v =>
        ite v (bind (turn (ih _ _ body hc.2)) fun g => ite g hl (pure _)) (pure _)
    case «loop» body =>
      exact bind (turn (ih _ _ body hc)) fun g => ite g (ih loops rets (.loop body) (by simp only [Expr.exits, hc])) (pure _)
    case «break» => exact jump hc
    case «continue» => exact jump hc
    case «return» e => exact bind (ih _ _ e hc.2) fun v => jump hc.1
    case perform op e => exact bind (ih _ _ e hc) fun v _ w _ => trivial
    case withH E c h b =>
      exact bind (ih _ _ h hc.1) fun _ s => Outcome.Exits.letGo M _
        (Outcome.Exits.handleWith M (fun f v s' => callAs M D _ c f _ s') (ih _ _ b hc.2 s))
    case held ns hs b =>
      exact bind (list ih hs hc.1) fun _ => bind (ofExcept _) fun _ =>
        bind (bind (world M _) asList) fun _ => by
          split
          · exact withVars M (fun s => Outcome.Exits.release M _ (ih _ _ b hc.2 s)) _
          · exact fail _

end Stilt
