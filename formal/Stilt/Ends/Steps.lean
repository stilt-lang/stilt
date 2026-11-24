import Stilt.Semantics

/-!
# Steps that end

`Eval.Ends P m`: from any state, `m` doesn't run out of fuel, and a value it
ends with is one that `P` holds of. Each combinator of `Stilt.Semantics` keeps
it, in any model of memory: it reads no state, since how much fuel a step takes
doesn't depend on the values it meets.
-/

namespace Stilt

/-- An outcome short of fuel is the one that `Ends` rules out, and so is a
performance: performing an operation is a site of `div`
(handlers.implicit-effects-and-capabilities), which code that ends never
reaches. -/
def Outcome.Ends {σ α : Type} (P : α → Prop) : Outcome σ α → Prop
  | .done a _ => P a
  | .outOfFuel => False
  | .performed .. => False
  | _ => True

/-- From any state, `m` doesn't run out of fuel, and ends with values of `P`. -/
def Eval.Ends {σ α : Type} (P : α → Prop) (m : Eval σ α) : Prop := ∀ s, Outcome.Ends P (m s)

namespace Eval.Ends

variable {σ α β : Type} {P : α → Prop} {Q : β → Prop}

theorem fault (f : Fault) (s : σ) : Outcome.Ends P (Outcome.fault f s : Outcome σ α) := by
  cases f <;> trivial

theorem pure {a : α} (h : P a) : Eval.Ends P (Pure.pure a : Eval σ α) := fun _ => h

theorem bind {m : Eval σ α} {f : α → Eval σ β} (hm : Eval.Ends P m)
    (hf : ∀ a, P a → Eval.Ends Q (f a)) : Eval.Ends Q (m >>= f) := by
  intro s
  show Outcome.Ends Q (Eval.bind m f s)
  have h := hm s
  unfold Eval.bind Outcome.bind
  split <;> simp_all [Outcome.Ends]
  rename_i a s' _
  exact hf a h s'

theorem fail (f : Fault) : Eval.Ends P (Eval.fail f : Eval σ α) := fun s => fault f s

theorem ofExcept (x : Except Fault α) (h : ∀ a, x = .ok a → P a) :
    Eval.Ends P (Eval.ofExcept x : Eval σ α) := by
  intro s
  cases x with
  | ok a => exact h a rfl
  | error f => exact fault f s

/-- Reading and writing the world ends, in any model of memory. -/
theorem world (M : Memory σ) (f : World → Except Fault (Value × World)) :
    Eval.Ends (fun _ => True) (Eval.world M f) := by
  intro s
  unfold Eval.world
  split
  · trivial
  · exact fault _ s

theorem inspect (f : σ → Except Fault α) (h : ∀ s a, f s = .ok a → P a) :
    Eval.Ends P (Eval.inspect f) := fun s => ofExcept (f s) (h s) s

theorem update (f : σ → Except Fault σ) : Eval.Ends (fun _ => True) (Eval.update f) := by
  intro s
  unfold Eval.update
  cases f s <;> first | trivial | exact fault _ s

theorem throw (e : Value) : Eval.Ends P (Eval.throw e : Eval σ α) := fun _ => trivial

theorem jump (j : Jump) : Eval.Ends P (Eval.jump j : Eval σ α) := fun _ => trivial

theorem handle {m : Eval σ α} {h : Value → Eval σ α} (hm : Eval.Ends P m)
    (hh : ∀ e, Eval.Ends P (h e)) : Eval.Ends P (Eval.handle m h) := by
  intro s
  have := hm s
  unfold Eval.handle Outcome.handle
  split
  · rename_i e s' _; exact hh e s'
  · simp_all [Outcome.Ends]
  · exact this

theorem turn {R : Value → Prop} {m : Eval σ Value} (hm : Eval.Ends R m) :
    Eval.Ends (fun _ => True) (Eval.turn m) := by
  intro s
  have h := hm s
  unfold Eval.turn Outcome.turn
  split <;> simp_all [Outcome.Ends]

theorem forEach {body : Value → Eval σ Bool} (hb : ∀ v, Eval.Ends (fun _ => True) (body v)) :
    ∀ vs : List Value, Eval.Ends (fun _ => True) (Eval.forEach body vs)
  | [] => pure trivial
  | v :: vs => by
    unfold Eval.forEach
    refine bind (hb v) fun b _ => ?_
    cases b
    · exact pure trivial
    · exact forEach hb vs

theorem ite (b : Bool) {m₁ m₂ : Eval σ α} (h₁ : Eval.Ends P m₁) (h₂ : Eval.Ends P m₂) :
    Eval.Ends P (if b then m₁ else m₂) := by
  cases b
  · exact h₂
  · exact h₁

section

variable (M : Memory σ)

theorem withVar (x : Name) (v : Value) {m : Eval σ α} (hm : Eval.Ends P m) :
    Eval.Ends P (Eval.withVar M x v m) := by
  intro s
  have h := hm (M.bind s x v)
  unfold Eval.withVar Outcome.unbind
  split <;> simp_all [Outcome.Ends]

theorem withInit (x : Name) (init : Expr) (v : Value) {m : Eval σ α} (hm : Eval.Ends P m) :
    Eval.Ends P (Eval.withInit M x init v m) := by
  intro s
  have h := hm (M.bindInit s x init v)
  unfold Eval.withInit Outcome.unbind
  split <;> simp_all [Outcome.Ends]

theorem withVars {m : Eval σ α} (hm : Eval.Ends P m) :
    ∀ bs : List (Name × Value), Eval.Ends P (Eval.withVars M bs m)
  | [] => hm
  | (x, v) :: bs => withVar M x v (withVars hm bs)

/-- A call whose body ends ends: entering and leaving it take no fuel. -/
theorem invoke (captured : List (Name × Value)) (params : List Param) (passed : List Passed)
    {body : Eval σ Value} (hb : Eval.Ends (fun _ => True) body) :
    Eval.Ends (fun _ => True) (Eval.invoke M captured params passed body) := by
  intro s
  unfold Eval.invoke Outcome.leaveCall
  cases bindArgs params passed with
  | none => trivial
  | some bound =>
    dsimp only
    cases M.enter s captured bound with
    | error f => exact fault f s
    | ok callee =>
      dsimp only
      have h := hb callee
      cases hr : body callee <;> rw [hr] at h <;> (try dsimp only)
      all_goals first
        | exact h
        | trivial
        | (split <;> first | trivial | exact fault _ _)
        | (rename_i j _; cases j <;> dsimp only <;> (try split) <;> first | trivial | exact fault _ _)

end

end Eval.Ends

end Stilt
