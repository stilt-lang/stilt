import Stilt.Semantics

/-!
# Fuel

More fuel never changes an outcome that less fuel reached. So an evaluation
that ends with a value, a raise, a jump, a panic or `stuck` has found the program's
one outcome, and `outOfFuel` says only that the fuel ran out first. A
performance's rest, resumed with any value, is again below. The theorems hold in every model of memory, the two of `Stilt.Memory` included.
-/

namespace Stilt

variable {σ α β : Type}

/-- `o` is `o'`, or `o` ran out of fuel on the way to it: a performance is
one of the same operation, argument and state, whose rest, resumed with any
value, is below the other's. -/
def Outcome.Below : Outcome σ α → Outcome σ α → Prop
  | .outOfFuel, _ => True
  | .done a s, o' => o' = .done a s
  | .raised e s, o' => o' = .raised e s
  | .jumped j s, o' => o' = .jumped j s
  | .panicked k s, o' => o' = .panicked k s
  | .performed op v s k, .performed op' v' s' k' =>
    op = op' ∧ v = v' ∧ s = s' ∧ ∀ w x, (k w x).Below (k' w x)
  | .performed .., _ => False
  | .stuck, o' => o' = .stuck

theorem Outcome.Below.refl : ∀ o : Outcome σ α, o.Below o
  | .done .. | .raised .. | .jumped .. | .panicked .. | .outOfFuel | .stuck => by
    simp [Outcome.Below]
  | .performed _ _ _ k => ⟨rfl, rfl, rfl, fun w x => Outcome.Below.refl (k w x)⟩

/-- An outcome below another is that one, or ran out of fuel, or is a
performance of the other's operation whose rest is below the other's. -/
theorem Outcome.Below.cases {o o' : Outcome σ α} (h : o.Below o') :
    o = .outOfFuel ∨ o = o' ∨
      ∃ op v s k k', o = .performed op v s k ∧ o' = .performed op v s k' ∧
        ∀ w x, (k w x).Below (k' w x) := by
  cases o with
  | outOfFuel => exact .inl rfl
  | performed op v s k =>
    cases o' with
    | performed op' v' s' k' =>
      obtain ⟨rfl, rfl, rfl, hk⟩ := h
      exact .inr (.inr ⟨_, _, _, _, _, rfl, rfl, hk⟩)
    | _ => exact h.elim
  | _ => exact .inr (.inl h.symm)

/-- A step after outcomes below each other keeps them so. -/
theorem Outcome.Below.bind {o o' : Outcome σ α} {f f' : α → σ → Outcome σ β} (h : o.Below o')
    (hf : ∀ a s, (f a s).Below (f' a s)) : (o.bind f).Below (o'.bind f') := by
  induction o generalizing o' with
  | performed op v s k ih =>
    cases o' with
    | performed op' v' s' k' =>
      obtain ⟨rfl, rfl, rfl, hk⟩ := h
      exact ⟨rfl, rfl, rfl, fun w x => ih w x (hk w x)⟩
    | _ => exact h.elim
  | outOfFuel => trivial
  | done a s => cases (show o' = _ from h); exact hf a s
  | _ => cases (show o' = _ from h); exact Outcome.Below.refl _

theorem Outcome.Below.handle {o o' : Outcome σ α} {h h' : Value → σ → Outcome σ α}
    (ho : o.Below o') (hh : ∀ e s, (h e s).Below (h' e s)) :
    (o.handle h).Below (o'.handle h') := by
  induction o generalizing o' with
  | performed op v s k ih =>
    cases o' with
    | performed op' v' s' k' =>
      obtain ⟨rfl, rfl, rfl, hk⟩ := ho
      exact ⟨rfl, rfl, rfl, fun w x => ih w x (hk w x)⟩
    | _ => exact ho.elim
  | outOfFuel => trivial
  | raised e s => cases (show o' = _ from ho); exact hh e s
  | _ => cases (show o' = _ from ho); exact Outcome.Below.refl _

theorem Outcome.Below.turn {o o' : Outcome σ Value} (h : o.Below o') :
    o.turn.Below o'.turn := by
  induction o generalizing o' with
  | performed op v s k ih =>
    cases o' with
    | performed op' v' s' k' =>
      obtain ⟨rfl, rfl, rfl, hk⟩ := h
      exact ⟨rfl, rfl, rfl, fun w x => ih w x (hk w x)⟩
    | _ => exact h.elim
  | outOfFuel => trivial
  | _ => cases (show o' = _ from h); exact Outcome.Below.refl _

theorem Outcome.Below.unbind (M : Memory σ) {o o' : Outcome σ α} (h : o.Below o') :
    (o.unbind M).Below (o'.unbind M) := by
  induction o generalizing o' with
  | performed op v s k ih =>
    cases o' with
    | performed op' v' s' k' =>
      obtain ⟨rfl, rfl, rfl, hk⟩ := h
      exact ⟨rfl, rfl, rfl, fun w x => ih w x (hk w x)⟩
    | _ => exact h.elim
  | outOfFuel => trivial
  | _ => cases (show o' = _ from h); exact Outcome.Below.refl _

theorem Outcome.Below.leaveCall (M : Memory σ) (bound : List (Name × Passed)) (s : σ)
    {o o' : Outcome σ Value} (h : o.Below o') :
    (o.leaveCall M bound s).Below (o'.leaveCall M bound s) := by
  induction o generalizing o' with
  | performed op v s' k ih =>
    cases o' with
    | performed op' v' s'' k' =>
      obtain ⟨rfl, rfl, rfl, hk⟩ := h
      unfold Outcome.leaveCall
      split
      · exact ⟨rfl, rfl, rfl, fun w x => ih w x (hk w x)⟩
      · exact Outcome.Below.refl _
    | _ => exact h.elim
  | outOfFuel => trivial
  | _ => cases (show o' = _ from h); exact Outcome.Below.refl _

theorem Outcome.Below.lift (M : Memory σ) (s : σ) {o o' : Outcome σ α} (h : o.Below o') :
    (o.lift M s).Below (o'.lift M s) := by
  induction o generalizing o' with
  | performed op v s₁ k ih =>
    cases o' with
    | performed op' v' s' k' =>
      obtain ⟨rfl, rfl, rfl, hk⟩ := h
      exact ⟨rfl, rfl, rfl, fun w x => ih w x (hk w x)⟩
    | _ => exact h.elim
  | outOfFuel => trivial
  | _ => cases (show o' = _ from h); exact Outcome.Below.refl _

theorem Outcome.Below.runBody (M : Memory σ) {resume resume' : Value → World → Outcome σ Value}
    (hr : ∀ u x, (resume u x).Below (resume' u x)) {o o' : Outcome σ Value} (h : o.Below o') :
    (o.runBody M resume).Below (o'.runBody M resume') := by
  induction o generalizing o' with
  | performed op u s k ih =>
    cases o' with
    | performed op' u' s' k' =>
      obtain ⟨rfl, rfl, rfl, hk⟩ := h
      unfold Outcome.runBody
      split
      · exact (hr u _).bind fun r s₃ => Outcome.Below.lift M s₃ (ih r _ (hk r _))
      · exact ⟨rfl, rfl, rfl, fun w x => ih w x (hk w x)⟩
    | _ => exact h.elim
  | outOfFuel => trivial
  | _ => cases (show o' = _ from h); exact Outcome.Below.refl _

/-- A `with` needs no more fuel than its block and its clauses do. -/
theorem Outcome.Below.handleWith (M : Memory σ) (effect : Name) (control : Bool) (hv : Value)
    {call call' : Value → Value → σ → Outcome σ Value}
    (hcall : ∀ c v s, (call c v s).Below (call' c v s)) {o o' : Outcome σ Value}
    (h : o.Below o') :
    (o.handleWith M effect control hv call).Below (o'.handleWith M effect control hv call') := by
  induction o generalizing o' with
  | performed op v s k ih =>
    cases o' with
    | performed op' v' s' k' =>
      obtain ⟨rfl, rfl, rfl, hk⟩ := h
      unfold Outcome.handleWith
      split
      · cases hv.clause? op.name with
        | none => exact Outcome.Below.refl _
        | some c =>
          dsimp only
          split
          · exact Outcome.Below.runBody M (fun u x => ih u x (hk u x)) (hcall c v s)
          · exact (hcall c v s).bind fun w _ => ih w _ (hk w _)
      · exact ⟨rfl, rfl, rfl, fun w x => ih w x (hk w x)⟩
    | _ => exact h.elim
  | outOfFuel => trivial
  | _ => cases (show o' = _ from h); exact Outcome.Below.refl _

/-- Ending a body keeps outcomes below each other, and leaves none that is a
performance: one that doesn't run out of fuel is the other. -/
theorem Outcome.Below.leaveBody {o o' : Outcome σ Value} (h : o.Below o')
    (ho : o.leaveBody ≠ .outOfFuel) : o'.leaveBody = o.leaveBody := by
  rcases h.cases with rfl | rfl | ⟨op, v, s, k, k', rfl, rfl, -⟩
  · exact absurd rfl ho
  · rfl
  · rfl

/-- Each outcome of `m` is the outcome of `m'` from the same state, or ran
out of fuel. -/
def Eval.Below (m m' : Eval σ α) : Prop := ∀ s, (m s).Below (m' s)

namespace Eval.Below

theorem refl (m : Eval σ α) : m.Below m := fun _ => Outcome.Below.refl _

theorem outOfFuel (m : Eval σ α) : (Eval.outOfFuel : Eval σ α).Below m := fun _ => trivial

theorem bind {m m' : Eval σ α} {f f' : α → Eval σ β} (hm : m.Below m')
    (hf : ∀ a, (f a).Below (f' a)) : (m >>= f).Below (m' >>= f') := fun s =>
  (hm s).bind fun a => hf a

theorem ite (b : Bool) {m₁ m₁' m₂ m₂' : Eval σ α} (h₁ : m₁.Below m₁')
    (h₂ : m₂.Below m₂') : (if b then m₁ else m₂).Below (if b then m₁' else m₂') := by
  cases b
  · exact h₂
  · exact h₁

theorem withVar (M : Memory σ) (x : Name) (v : Value) {m m' : Eval σ α}
    (hm : m.Below m') : (Eval.withVar M x v m).Below (Eval.withVar M x v m') := fun s =>
  (hm (M.bind s x v)).unbind M

theorem _root_.Stilt.Outcome.Below.release (M : Memory σ) (cells : List (Name × Ty × Nat))
    {o o' : Outcome σ α} (h : o.Below o') : (o.release M cells).Below (o'.release M cells) := by
  induction o generalizing o' with
  | performed op v s k ih =>
    cases o' with
    | performed op' v' s' k' =>
      obtain ⟨rfl, rfl, rfl, hk⟩ := h
      simp only [Outcome.release, Outcome.after]
      split
      · exact ⟨rfl, rfl, rfl, fun w x => ih w x (hk w x)⟩
      · exact Outcome.Below.refl _
    | _ => exact h.elim
  | outOfFuel => trivial
  | _ => cases (show o' = _ from h); exact Outcome.Below.refl _

theorem _root_.Stilt.Outcome.Below.letGo (M : Memory σ) (before : World) {o o' : Outcome σ α}
    (h : o.Below o') : (o.letGo M before).Below (o'.letGo M before) := by
  induction o generalizing o' with
  | performed op v s k ih =>
    cases o' with
    | performed op' v' s' k' =>
      obtain ⟨rfl, rfl, rfl, hk⟩ := h
      exact ⟨rfl, rfl, rfl, fun w x => ih w x (hk w x)⟩
    | _ => exact h.elim
  | outOfFuel => trivial
  | _ => cases (show o' = _ from h); exact Outcome.Below.refl _

theorem withInit (M : Memory σ) (x : Name) (init : Expr) (v : Value) {m m' : Eval σ α}
    (hm : m.Below m') : (Eval.withInit M x init v m).Below (Eval.withInit M x init v m') :=
  fun s => (hm (M.bindInit s x init v)).unbind M

theorem withVars (M : Memory σ) {m m' : Eval σ α} (hm : m.Below m') :
    ∀ bindings, (Eval.withVars M bindings m).Below (Eval.withVars M bindings m')
  | [] => hm
  | (x, v) :: bindings => withVar M x v (withVars M hm bindings)

theorem handle {m m' : Eval σ α} {h h' : Value → Eval σ α} (hm : m.Below m')
    (hh : ∀ e, (h e).Below (h' e)) : (Eval.handle m h).Below (Eval.handle m' h') := fun s =>
  (hm s).handle fun e => hh e

theorem turn {m m' : Eval σ Value} (hm : m.Below m') : (Eval.turn m).Below (Eval.turn m') :=
  fun s => (hm s).turn

theorem forEach {body body' : Value → Eval σ Bool} (h : ∀ v, (body v).Below (body' v)) :
    ∀ vs, (Eval.forEach body vs).Below (Eval.forEach body' vs)
  | [] => refl _
  | v :: vs => bind (h v) fun b => ite b (forEach h vs) (refl _)

theorem invoke (M : Memory σ) (captured : List (Name × Value)) (params : List Param)
    (args : List Passed) {body body' : Eval σ Value} (h : body.Below body') :
    (Eval.invoke M captured params args body).Below (Eval.invoke M captured params args body') := by
  intro s
  unfold Eval.invoke
  split
  · exact Outcome.Below.refl _
  · split
    · exact Outcome.Below.refl _
    · rename_i callee _
      exact (h callee).leaveCall M _ s

/-- The combinators below take the evaluation of a subexpression as `run`;
each is monotone in it. -/
abbrev Runs (run run' : Expr → Eval σ Value) : Prop := ∀ e, (run e).Below (run' e)

theorem call (D : Decls) (M : Memory σ) {run run' : Expr → Eval σ Value} (h : Runs run run')
    (f : Value) (args : List Passed) :
    (Eval.call D M run f args).Below (Eval.call D M run' f args) := by
  unfold Eval.call
  split
  · exact invoke M _ _ _ (h _)
  · split
    · exact invoke M _ _ _ (h _)
    · exact refl _
  · exact refl _

theorem callAs (D : Decls) (M : Memory σ) {run run' : Expr → Eval σ Value} (h : Runs run run')
    (control : Bool) (f : Value) (args : List Passed) :
    (Eval.callAs D M run control f args).Below (Eval.callAs D M run' control f args) := by
  unfold Eval.callAs
  split
  · exact refl _
  · exact call D M h f args

theorem list {run run' : Expr → Eval σ Value} (h : Runs run run') :
    ∀ es, (Eval.list run es).Below (Eval.list run' es)
  | [] => refl _
  | e :: es => bind (h e) fun _ => bind (list h es) fun _ => refl _

theorem fields {run run' : Expr → Eval σ Value} (h : Runs run run') :
    ∀ fs, (Eval.fields run fs).Below (Eval.fields run' fs)
  | [] => refl _
  | (_, e) :: fs => bind (h e) fun _ => bind (fields h fs) fun _ => refl _

theorem path {run run' : Expr → Eval σ Value} (h : Runs run run') :
    ∀ ps, (Eval.path run ps).Below (Eval.path run' ps)
  | [] => refl _
  | .field _ :: ps => bind (path h ps) fun _ => refl _
  | .index i :: ps =>
    bind (bind (h i) fun _ => refl _) fun _ => bind (path h ps) fun _ => refl _

theorem args {run run' : Expr → Eval σ Value} (h : Runs run run') :
    ∀ as, (Eval.args run as).Below (Eval.args run' as)
  | [] => refl _
  | .value e :: as => bind (h e) fun _ => bind (args h as) fun _ => refl _
  | .inout ⟨_, ps⟩ :: as => bind (path h ps) fun _ => bind (args h as) fun _ => refl _

theorem select (M : Memory σ) {run run' : Expr → Eval σ Value} (h : Runs run run')
    (arms : List Arm) (v : Value) :
    (Eval.select M run arms v).Below (Eval.select M run' arms v) := by
  unfold Eval.select
  split
  · split
    · exact withVars M (h _) _
    · exact refl _
  · exact refl _

theorem assign (M : Memory σ) {run run' : Expr → Eval σ Value} (h : Runs run run') (x : Name)
    (ps : List Projection) (value : Expr) :
    (Eval.assign M run x ps value).Below (Eval.assign M run' x ps value) :=
  bind (path h ps) fun _ => bind (h value) fun _ => bind (refl _) fun _ => refl _

theorem loop (M : Memory σ) {run run' : Expr → Eval σ Value} (h : Runs run run') (x : Name)
    (e body : Expr) : (Eval.loop M run x e body).Below (Eval.loop M run' x e body) :=
  bind (bind (h e) fun _ => refl _) fun vs =>
    bind (forEach (fun v => withVar M x v (turn (h body))) vs) fun _ => refl _

end Eval.Below

/-- Evaluation with more fuel reaches every outcome that evaluation with less
fuel reaches, other than running out. -/
theorem eval_mono (D : Decls) (M : Memory σ) :
    ∀ {n m : Nat}, n ≤ m → ∀ e, (eval D M n e).Below (eval D M m e)
  | 0, _, _, _ => Eval.Below.outOfFuel _
  | _ + 1, 0, h, _ => absurd h (by omega)
  | n + 1, m + 1, h, e => by
    have ih : Eval.Below.Runs (eval D M n) (eval D M m) := eval_mono D M (by omega)
    open Eval.Below in
    cases e with
    | var x => exact refl _
    | move x => exact refl _
    | int k => exact refl _
    | bool b => exact refl _
    | unit => exact refl _
    | record R fs => exact bind (fields ih fs) fun _ => refl _
    | variant T C es => exact bind (list ih es) fun _ => refl _
    | list τ es => exact bind (list ih es) fun _ => refl _
    | op o es => exact bind (list ih es) fun _ => refl _
    | view es => exact bind (list ih es) fun _ => refl _
    | field e f => exact bind (ih e) fun _ => refl _
    | index e i => exact bind (ih e) fun _ => bind (bind (ih i) fun _ => refl _) fun _ => refl _
    | fnRef f types rows => exact refl _
    | method t m τ => exact refl _
    | closure ps r ρ body => exact refl _
    | call callee as =>
      exact bind (ih callee) fun _ => bind (args ih as) fun _ => callAs D M ih false _ _
    | letIn x τ init body => exact bind (ih init) fun _ => withInit M x init _ (ih body)
    | varIn x τ init body => exact bind (ih init) fun _ => withInit M x init _ (ih body)
    | assign p value =>
      obtain ⟨x, ps⟩ := p
      exact assign M ih x ps value
    | seq a b => exact bind (ih a) fun _ => ih b
    | «if» c τ a b => exact bind (bind (ih c) fun _ => refl _) fun v => ite v (ih a) (ih b)
    | «match» e τ arms => exact bind (ih e) fun v => select M ih arms v
    | «for» x τ e body => exact loop M ih x e body
    | raise e => exact bind (ih e) fun _ => refl _
    | «try» e => exact ih e
    | tryCatch e E x hd τ => exact handle (ih e) fun _ => withVar M x _ (ih hd)
    | «while» c body =>
      exact bind (bind (ih c) fun _ => refl _) fun v =>
        ite v (bind (turn (ih body)) fun g => ite g (ih _) (refl _)) (refl _)
    | «loop» body => exact bind (turn (ih body)) fun g => ite g (ih _) (refl _)
    | «break» => exact refl _
    | «continue» => exact refl _
    | «return» e => exact bind (ih e) fun _ => refl _
    | perform op e => exact bind (ih e) fun _ => refl _
    | withH E c hd b =>
      exact bind (ih hd) fun hv s => Outcome.Below.letGo M _
        (Outcome.Below.handleWith M E c hv (fun f v s => callAs D M ih c f [.value v] s) (ih b s))
    | held ns hs body =>
      exact bind (list ih hs) fun _ => bind (refl _) fun _ => bind (refl _) fun _ => by
        split
        · exact withVars M (fun s => (ih body s).release M _) _
        · exact refl _

/-- A run that reached an outcome other than running out of fuel reaches the
same outcome with any more fuel. -/
theorem Program.run_mono {M : Memory σ} {init : σ} {p : Program} {n m : Nat}
    (hnm : n ≤ m) (h : p.run M init n ≠ .outOfFuel) : p.run M init m = p.run M init n :=
  (eval_mono p.decls M hnm p.main init).leaveBody h

/-- A program has one outcome: two runs that don't run out of fuel reach the
same one, whatever fuel each had. -/
theorem Program.run_deterministic {M : Memory σ} {init : σ} {p : Program} {n m : Nat}
    (hn : p.run M init n ≠ .outOfFuel) (hm : p.run M init m ≠ .outOfFuel) :
    p.run M init n = p.run M init m := by
  rcases Nat.le_total n m with h | h
  · exact (Program.run_mono h hn).symm
  · exact Program.run_mono h hm

end Stilt
