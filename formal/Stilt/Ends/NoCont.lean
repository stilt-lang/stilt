import Stilt.Ends.Counting
import Stilt.Semantics

/-!
# Code that doesn't continue

Code free of `continue` outside its own loops and closure literals never ends
with a `continue` (`eval_noCont`), in any model of memory: a loop's turn takes
in the `continue`s of its body, and a call those of the body it runs.
-/

namespace Stilt

/-- An outcome that isn't a `continue`, nor a performance whose rest, resumed with
any value, may end with one. -/
def Outcome.NoCont {σ α : Type} : Outcome σ α → Prop
  | .jumped .cont _ => False
  | .performed _ _ _ k => ∀ w x, Outcome.NoCont (k w x)
  | _ => True

/-- `m` never ends with a `continue`, a performance's rest included. -/
def Eval.NoCont {σ α : Type} (m : Eval σ α) : Prop := ∀ s, (m s).NoCont

namespace Outcome.NoCont

variable {σ α β : Type}

theorem ne {o : Outcome σ α} (h : o.NoCont) (s : σ) : o ≠ .jumped .cont s := by
  rintro rfl
  exact h

theorem fault (f : Fault) (s : σ) : (Outcome.fault f s : Outcome σ α).NoCont := by
  cases f <;> trivial

theorem bind {f : α → σ → Outcome σ β} (hf : ∀ a s, (f a s).NoCont) :
    ∀ {o : Outcome σ α}, o.NoCont → (o.bind f).NoCont
  | .done a s, _ => hf a s
  | .performed _ _ _ _, h => fun w x => bind hf (h w x)
  | .jumped .cont _, h => h
  | .jumped .brk _, h | .jumped (.ret _) _, h | .raised _ _, h | .panicked _ _, h | .outOfFuel, h
  | .stuck, h => h

theorem handle {h : Value → σ → Outcome σ α} (hh : ∀ e s, (h e s).NoCont) :
    ∀ {o : Outcome σ α}, o.NoCont → (o.handle h).NoCont
  | .raised e s, _ => hh e s
  | .performed _ _ _ _, h' => fun w x => handle hh (h' w x)
  | .jumped .cont _, h' => h'
  | .done _ _, h' | .jumped .brk _, h' | .jumped (.ret _) _, h' | .panicked _ _, h' | .outOfFuel, h'
  | .stuck, h' => h'

theorem turn : ∀ o : Outcome σ Value, o.turn.NoCont
  | .performed _ _ _ k => fun w x => turn (k w x)
  | .jumped .cont _ | .jumped .brk _ | .jumped (.ret _) _ | .done _ _ | .raised _ _ | .panicked _ _
  | .outOfFuel | .stuck => trivial

theorem unbind (M : Memory σ) : ∀ {o : Outcome σ α}, o.NoCont → (o.unbind M).NoCont
  | .performed _ _ _ _, h => fun w x => unbind M (h w x)
  | .jumped .cont _, h => h
  | .done _ _, h | .jumped .brk _, h | .jumped (.ret _) _, h | .raised _ _, h | .panicked _ _, h
  | .outOfFuel, h | .stuck, h => h

/-- A call takes in its body's `continue`s. -/
theorem leaveCall (M : Memory σ) (bound : List (Name × Passed)) (s : σ) :
    ∀ o : Outcome σ Value, (o.leaveCall M bound s).NoCont
  | .done _ s' | .raised _ s' | .jumped (.ret _) s' | .panicked _ s' => by
    simp only [Outcome.leaveCall]
    split <;> first | trivial | exact fault _ _
  | .performed _ _ s' k => by
    simp only [Outcome.leaveCall]
    split
    · exact fun w x => leaveCall M bound s (k w x)
    · exact fault _ _
  | .jumped .brk _ | .jumped .cont _ | .outOfFuel | .stuck => trivial

theorem lift (M : Memory σ) (s : σ) : ∀ {o : Outcome σ α}, o.NoCont → (o.lift M s).NoCont
  | .performed _ _ _ _, h => fun w x => lift M s (h w x)
  | .jumped .cont _, h => h
  | .done _ _, h | .jumped .brk _, h | .jumped (.ret _) _, h | .raised _ _, h | .panicked _ _, h
  | .outOfFuel, h | .stuck, h => h

theorem runBody (M : Memory σ) {resume : Value → World → Outcome σ Value}
    (hr : ∀ u x, (resume u x).NoCont) :
    ∀ {o : Outcome σ Value}, o.NoCont → (o.runBody M resume).NoCont
  | .performed op u s k, h => by
    unfold Outcome.runBody
    split
    · exact bind (fun r s' => lift M s' (runBody M hr (h r _))) (hr u _)
    · exact fun w x => runBody M hr (h w x)
  | .jumped .cont _, h => h
  | .done _ _, h | .jumped .brk _, h | .jumped (.ret _) _, h | .raised _ _, h | .panicked _ _, h
  | .outOfFuel, h | .stuck, h => h

/-- A `with` whose block and clauses' calls never end with a `continue` never does. -/
theorem handleWith (M : Memory σ) {effect : Name} {control : Bool} {handler : Value}
    {call : Value → Value → σ → Outcome σ Value} (hcall : ∀ c v s, (call c v s).NoCont) :
    ∀ {o : Outcome σ Value}, o.NoCont → (o.handleWith M effect control handler call).NoCont
  | .performed op v s k, h => by
    unfold Outcome.handleWith
    split
    · split
      · trivial
      · split
        · exact runBody M (fun u x => handleWith M hcall (h u x)) (hcall _ v s)
        · exact bind (fun w _ => handleWith M hcall (h w _)) (hcall _ v s)
    · exact fun w x => handleWith M hcall (h w x)
  | .jumped .cont _, h => h
  | .done _ _, h | .jumped .brk _, h | .jumped (.ret _) _, h | .raised _ _, h | .panicked _ _, h
  | .outOfFuel, h | .stuck, h => h

theorem after {f : σ → Except Fault σ} {s : σ} {o : σ → Outcome σ α} (ho : ∀ s', (o s').NoCont) :
    (Outcome.after f s o).NoCont := by
  unfold Outcome.after
  split
  · exact ho _
  · exact fault _ _

theorem release (M : Memory σ) (cells : List (Name × Ty × Nat)) :
    ∀ {o : Outcome σ α}, o.NoCont → (o.release M cells).NoCont
  | .performed _ _ _ _, h => after fun _ w x => release M cells (h w x)
  | .jumped .cont _, h => nomatch h
  | .done _ _, _ | .jumped .brk _, _ | .jumped (.ret _) _, _ | .raised _ _, _ | .panicked _ _, _ =>
    after fun _ => trivial
  | .outOfFuel, h | .stuck, h => h

theorem letGo (M : Memory σ) (before : World) : ∀ {o : Outcome σ α}, o.NoCont → (o.letGo M before).NoCont
  | .performed _ _ _ _, h => fun w x => letGo M before (h w x)
  | .jumped .cont _, h => h
  | .done _ _, h | .jumped .brk _, h | .jumped (.ret _) _, h | .raised _ _, h | .panicked _ _, h
  | .outOfFuel, h | .stuck, h => h

end Outcome.NoCont

namespace Eval.NoCont

variable {σ α β : Type}

theorem pure (a : α) : Eval.NoCont (Pure.pure a : Eval σ α) := fun _ => trivial

theorem fail (f : Fault) : Eval.NoCont (Eval.fail f : Eval σ α) := fun s => Outcome.NoCont.fault f s

theorem ofExcept (x : Except Fault α) : Eval.NoCont (Eval.ofExcept x : Eval σ α) := by
  intro s
  cases x with
  | ok a => trivial
  | error f => exact Outcome.NoCont.fault f s

theorem inspect (f : σ → Except Fault α) : Eval.NoCont (Eval.inspect f) := fun s => ofExcept (f s) s

theorem world (M : Memory σ) (f : World → Except Fault (Value × World)) :
    Eval.NoCont (Eval.world M f) := by
  intro s
  unfold Eval.world
  split
  · trivial
  · exact Outcome.NoCont.fault _ s

theorem update (f : σ → Except Fault σ) : Eval.NoCont (Eval.update f) := by
  intro s
  unfold Eval.update
  cases f s
  · exact Outcome.NoCont.fault _ s
  · trivial

theorem throw (e : Value) : Eval.NoCont (Eval.throw e : Eval σ α) := fun _ => trivial

theorem ret (v : Value) : Eval.NoCont (Eval.jump (.ret v) : Eval σ α) := fun _ => trivial

theorem brk : Eval.NoCont (Eval.jump .brk : Eval σ α) := fun _ => trivial

theorem bind {m : Eval σ α} {f : α → Eval σ β} (hm : Eval.NoCont m) (hf : ∀ a, Eval.NoCont (f a)) :
    Eval.NoCont (m >>= f) := fun s => Outcome.NoCont.bind (fun a s' => hf a s') (hm s)

theorem ite (b : Bool) {m₁ m₂ : Eval σ α} (h₁ : Eval.NoCont m₁) (h₂ : Eval.NoCont m₂) :
    Eval.NoCont (if b then m₁ else m₂) := by
  cases b
  · exact h₂
  · exact h₁

theorem handle {m : Eval σ α} {h : Value → Eval σ α} (hm : Eval.NoCont m) (hh : ∀ e, Eval.NoCont (h e)) :
    Eval.NoCont (Eval.handle m h) := fun s => Outcome.NoCont.handle (fun e s' => hh e s') (hm s)

theorem turn (m : Eval σ Value) : Eval.NoCont (Eval.turn m) := fun s => Outcome.NoCont.turn (m s)

theorem forEach {body : Value → Eval σ Bool} (hb : ∀ v, Eval.NoCont (body v)) :
    ∀ vs, Eval.NoCont (Eval.forEach body vs)
  | [] => pure ()
  | v :: vs => by
    unfold Eval.forEach
    exact bind (hb v) fun b => ite b (forEach hb vs) (pure ())

theorem asBool (v : Value) : Eval.NoCont (Eval.asBool v : Eval σ Bool) := by
  cases v <;> first | exact pure _ | exact fail _

theorem asInt (v : Value) : Eval.NoCont (Eval.asInt v : Eval σ Int) := by
  cases v <;> first | exact pure _ | exact fail _

theorem asList (v : Value) : Eval.NoCont (Eval.asList v : Eval σ (List Value)) := by
  cases v <;> first | exact pure _ | exact fail _

section

variable (M : Memory σ)

theorem withVar (x : Name) (v : Value) {m : Eval σ α} (hm : Eval.NoCont m) :
    Eval.NoCont (Eval.withVar M x v m) := fun s => Outcome.NoCont.unbind M (hm (M.bind s x v))

theorem withInit (x : Name) (init : Expr) (v : Value) {m : Eval σ α} (hm : Eval.NoCont m) :
    Eval.NoCont (Eval.withInit M x init v m) := fun s =>
  Outcome.NoCont.unbind M (hm (M.bindInit s x init v))

theorem withVars {m : Eval σ α} (hm : Eval.NoCont m) :
    ∀ bs : List (Name × Value), Eval.NoCont (Eval.withVars M bs m)
  | [] => hm
  | (x, v) :: bs => withVar M x v (withVars hm bs)

/-- A call never ends with a `continue`: it takes in its body's. -/
theorem invoke (captured : List (Name × Value)) (params : List Param) (passed : List Passed)
    (body : Eval σ Value) : Eval.NoCont (Eval.invoke M captured params passed body) := by
  intro s
  unfold Eval.invoke
  split
  · trivial
  · split
    · exact Outcome.NoCont.fault _ s
    · exact Outcome.NoCont.leaveCall M _ s _

end

/-- Running an expression free of `continue` never ends with one. -/
def NoContRun (run : Expr → Eval σ Value) : Prop := ∀ e, e.contFree = true → Eval.NoCont (run e)

section Runs

variable (M : Memory σ) {run : Expr → Eval σ Value} (h : NoContRun run)
include h

theorem list : ∀ es : List Expr, exprsContFree es = true → Eval.NoCont (Eval.list run es)
  | [], _ => pure _
  | e :: es, hc => by
    simp only [exprsContFree, Bool.and_eq_true] at hc
    exact bind (h e hc.1) fun _ => bind (list es hc.2) fun _ => pure _

theorem fields : ∀ fs : List (Name × Expr), fieldsContFree fs = true → Eval.NoCont (Eval.fields run fs)
  | [], _ => pure _
  | (_, e) :: fs, hc => by
    simp only [fieldsContFree, Bool.and_eq_true] at hc
    exact bind (h e hc.1) fun _ => bind (fields fs hc.2) fun _ => pure _

theorem path : ∀ ps : List Projection, pathContFree ps = true → Eval.NoCont (Eval.path run ps)
  | [], _ => pure _
  | .field _ :: ps, hc => by
    simp only [pathContFree] at hc
    exact bind (path ps hc) fun _ => pure _
  | .index i :: ps, hc => by
    simp only [pathContFree, Bool.and_eq_true] at hc
    exact bind (bind (h i hc.1) fun v => asInt v) fun _ => bind (path ps hc.2) fun _ => pure _

theorem args : ∀ as : List Arg, argsContFree as = true → Eval.NoCont (Eval.args run as)
  | [], _ => pure _
  | .value e :: as, hc => by
    simp only [argsContFree, Bool.and_eq_true] at hc
    exact bind (h e hc.1) fun _ => bind (args as hc.2) fun _ => pure _
  | .inout ⟨_, ps⟩ :: as, hc => by
    simp only [argsContFree, Bool.and_eq_true] at hc
    exact bind (path h ps hc.1) fun _ => bind (args as hc.2) fun _ => pure _

omit h in
theorem arms_mem : ∀ {arms : List Arm} {arm : Arm}, armsContFree arms = true → arm ∈ arms →
    arm.body.contFree = true
  | ⟨_, _, _⟩ :: _, _, hc, hm => by
    simp only [armsContFree, Bool.and_eq_true] at hc
    rcases List.mem_cons.1 hm with rfl | hm
    · exact hc.1
    · exact arms_mem hc.2 hm

theorem select {arms : List Arm} (hc : armsContFree arms = true) (v : Value) :
    Eval.NoCont (Eval.select M run arms v) := by
  unfold Eval.select
  cases hsel : selectArm arms v with
  | none => exact fail _
  | some au =>
    obtain ⟨arm, us⟩ := au
    obtain ⟨hmem, -⟩ := selectArm_mem hsel
    dsimp only
    split
    · exact withVars M (h _ (arms_mem hc hmem)) _
    · exact fail _

theorem assign (x : Name) {ps : List Projection} (hp : pathContFree ps = true) {value : Expr}
    (hv : value.contFree = true) : Eval.NoCont (Eval.assign M run x ps value) :=
  bind (path h ps hp) fun _ => bind (h value hv) fun _ => bind (update _) fun _ => pure _

theorem loop (x : Name) {e : Expr} (he : e.contFree = true) (body : Expr) :
    Eval.NoCont (Eval.loop M run x e body) :=
  bind (bind (h e he) fun v => asList v) fun vs =>
    bind (forEach (fun v => withVar M x v (turn _)) vs) fun _ => pure _

end Runs

theorem call (D : Decls) (M : Memory σ) (run : Expr → Eval σ Value) (f : Value) (passed : List Passed) :
    Eval.NoCont (Eval.call D M run f passed) := by
  unfold Eval.call
  split
  · exact invoke M _ _ _ _
  · split
    · exact invoke M _ _ _ _
    · exact fail _
  · exact fail _

theorem callAs (D : Decls) (M : Memory σ) (run : Expr → Eval σ Value) (control : Bool) (f : Value)
    (passed : List Passed) : Eval.NoCont (Eval.callAs D M run control f passed) := by
  unfold Eval.callAs
  split
  · exact fail _
  · exact call D M run f passed

end Eval.NoCont

open Eval.NoCont in
/-- Evaluating code free of `continue`, with any fuel, never ends with a `continue`,
a performance's rest included. -/
theorem eval_noCont {σ : Type} (D : Decls) (M : Memory σ) : ∀ n, NoContRun (eval D M n)
  | 0, _, _ => fun _ => trivial
  | n + 1, e, hc => by
    have ih := eval_noCont D M n
    cases e <;> try simp only [Expr.contFree, Bool.and_eq_true] at hc
    case var x => exact inspect _
    case move x => exact inspect _
    case int k | bool b | unit => exact pure _
    case record R _ fs =>
      exact bind (fields ih fs hc) fun _ => by
        show Eval.NoCont (Eval.declare D R _)
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
    case field e f => exact bind (ih e hc) fun _ => ofExcept _
    case index e i => exact bind (ih e hc.1) fun _ => bind (bind (ih i hc.2) fun v => asInt v) fun _ => ofExcept _
    case fnRef f types rows => exact pure _
    case method t m τ =>
      show Eval.NoCont (Eval.method D t m τ)
      unfold Eval.method
      split
      · split
        · exact pure _
        · exact fail _
      · exact fail _
    case closure ps result ρ body => exact bind (inspect _) fun _ => pure _
    case call callee as _ => exact bind (ih callee hc.1) fun f => bind (args ih as hc.2) fun ps => callAs D M _ false f ps
    case letIn x τ init body => exact bind (ih init hc.1) fun v => withInit M x init v (ih body hc.2)
    case varIn x τ init body => exact bind (ih init hc.1) fun v => withInit M x init v (ih body hc.2)
    case assign p value =>
      obtain ⟨x, ps⟩ := p
      simp only [Expr.contFree, Bool.and_eq_true] at hc
      exact assign M ih x hc.1 hc.2
    case seq a b => exact bind (ih a hc.1) fun _ => ih b hc.2
    case «if» c τ a b => exact bind (bind (ih c hc.1.1) fun v => asBool v) fun v => ite v (ih a hc.1.2) (ih b hc.2)
    case «match» e τ arms => exact bind (ih e hc.1) fun v => select M ih hc.2 v
    case «for» x τ e body => exact loop M ih x hc body
    case raise e => exact bind (ih e hc) fun v => throw v
    case «try» e => exact ih e hc
    case form _ e => exact ih e hc
    case tryCatch e E x h τ => exact handle (ih e hc.1) fun err => withVar M x err (ih h hc.2)
    case «while» c body =>
      have hl := ih (.while c body) (by simpa [Expr.contFree] using hc)
      exact bind (bind (ih c hc) fun v => asBool v) fun v =>
        ite v (bind (turn _) fun g => ite g hl (pure _)) (pure _)
    case «loop» body => exact bind (turn _) fun g => ite g (ih (.loop body) rfl) (pure _)
    case «break» => exact brk
    case «continue» => cases hc
    case «return» e => exact bind (ih e hc) fun v => ret v
    case perform op e => exact bind (ih e hc) fun v _ w _ => trivial
    case withH E c h b =>
      exact bind (ih h hc.1) fun _ s => Outcome.NoCont.letGo M _
        (Outcome.NoCont.handleWith M (fun f v s' => callAs D M _ c f _ s') (ih b hc.2 s))
    case held ns hs b =>
      exact bind (list ih hs hc.1) fun _ => bind (ofExcept _) fun _ =>
        bind (bind (world M _) asList) fun _ => by
          split
          · exact withVars M (fun s => Outcome.NoCont.release M _ (ih b hc.2 s)) _
          · exact fail _

end Stilt
