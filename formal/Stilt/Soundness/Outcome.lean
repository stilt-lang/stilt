import Stilt.Soundness.Paths
import Stilt.Semantics

/-!
# Sound outcomes

What type soundness allows a step of the copy-in, copy-out evaluator to end
with, from a frame of its context: a value that the step's property holds of,
a raise of an error type that its effects allow, or a jump that they allow,
each with a frame of the same context; a panic; or running out of fuel. Never
`stuck`. The lemmas show that the evaluator's combinators keep it.
-/

namespace Stilt

/-- The error types that code where `fx` holds may raise, under `η`: inside the
operand of a `catch`, the caught type, since effects.catch-around-row-variables lets a call
through a row variable there only when the signature pairs it with that type;
elsewhere, every error type its row can raise (effects.missing-effects and effects.catch-around-row-variables). -/
def Effects.raises (η : REnv) (fx : Effects) : List STy :=
  if fx.catching then (fx.row.raise.map (Ty.close η)).toList else fx.row.close η

/-- Where a step may leave other than at its end: the error types it may
raise, the jumps it may make, and the operations it may perform, each with the
type of its argument and of the value that resumes it
(handlers.performing-operation). -/
structure Exits where
  raises : List STy
  jumps : Jump → Prop
  performs : Operation → STy → STy → Prop

/-- The operations that code whose row reads as `L` at run time may perform,
with the types of their argument and of the value that resumes them: `resume`,
at the types of the row's label for it, and an operation of an effect whose
label the row holds, at the types the effect declares
(handlers.performing-operation and handlers.resuming). -/
def performsOf (D : Decls) (L : List STy) (op : Operation) (τ ρ : STy) : Prop :=
  if op = Operation.resume then ∃ B R, .resume B R ∈ L ∧ τ = B.sem ∧ ρ = R.sem
  else .effect op.effect ∈ L ∧ ∃ A B, D.operation? op = some (A, B) ∧ τ = A.sem ∧ ρ = B.sem

theorem performsOf_resume {D : Decls} {L : List STy} {τ ρ : STy} :
    performsOf D L .resume τ ρ ↔ ∃ B R, .resume B R ∈ L ∧ τ = B.sem ∧ ρ = R.sem := by
  simp [performsOf]

theorem performsOf_of_ne {D : Decls} {L : List STy} {op : Operation} {τ ρ : STy}
    (hne : op ≠ .resume) :
    performsOf D L op τ ρ ↔
      .effect op.effect ∈ L ∧ ∃ A B, D.operation? op = some (A, B) ∧ τ = A.sem ∧ ρ = B.sem := by
  simp [performsOf, hne]

/-- Rows with the same labels perform the same operations. -/
theorem performsOf_of_labels {D : Decls} {L L' : List STy} (h : ∀ x ∈ L, x.IsLabel → x ∈ L')
    {op : Operation} {τ ρ : STy} (hp : performsOf D L op τ ρ) : performsOf D L' op τ ρ := by
  by_cases hr : op = Operation.resume
  · subst hr
    obtain ⟨B, R, hm, h₁, h₂⟩ := performsOf_resume.1 hp
    exact performsOf_resume.2 ⟨B, R, h _ hm trivial, h₁, h₂⟩
  · obtain ⟨hm, h'⟩ := (performsOf_of_ne hr).1 hp
    exact (performsOf_of_ne hr).2 ⟨h _ hm trivial, h'⟩

/-- A world whose cells hold values of their types, each type read with no row variable
(shared.std-sync and `Stilt.World`). -/
def World.Typed (D : Decls) (w : World) : Prop :=
  ∀ c ∈ w.cells, Value.Typed D c.value c.type.sem

/-- A state of copy-in, copy-out whose frame holds values of its context's types, in a
typed world. -/
def State.Typed (D : Decls) (γ : Copy.State) (Γ : Ctx) (η : REnv) : Prop :=
  Frame.Typed D γ.1 Γ η ∧ World.Typed D γ.2

/-- A new cell holding a value of its type keeps a world typed. -/
theorem World.Typed.push {D : Decls} {w : World} (hw : World.Typed D w) {u : Ty} {v : Value}
    (hv : Value.Typed D v u.sem) : World.Typed D (w.push u v) := by
  intro c hc
  rcases List.mem_append.1 hc with hc | hc
  · exact hw c hc
  · obtain rfl := List.mem_singleton.1 hc
    exact hv

section

variable {D : Decls} {α β : Type}

/-- The jumps that code where `fx` holds may make, under `η`: a `break` or a
`continue` inside a loop's body (expressions.break-and-continue), and a
`return` with a value of its body's result type (expressions.closure-boundaries). -/
def Effects.jumps (D : Decls) (η : REnv) (fx : Effects) : Jump → Prop
  | .brk => fx.breaks = true
  | .cont => fx.continues = true
  | .ret v => Value.Typed D v (fx.result.close η)

/-- Where code where `fx` holds may leave, under `η`: the operations it may
perform are those its row allows, the catch around it notwithstanding. -/
def Effects.exits (D : Decls) (η : REnv) (fx : Effects) : Exits :=
  ⟨fx.raises η, fx.jumps D η, performsOf D (fx.row.close η)⟩

/-- An outcome that type soundness allows, from a frame of `Γ`: a value, a
raise, a jump or a panic (effects.panic-kinds) that leaves a frame of `Γ`
(expressions.scope) in a typed world; a performance of an operation that its exits allow,
on an argument of the operation's type, that leaves such a state and whose rest is
again such an outcome once resumed with a value of the type the operation
gives, in a typed world; or running out of fuel. -/
def Outcome.Ok (D : Decls) (Γ : Ctx) (η : REnv) (X : Exits) (P : α → Prop) :
    Outcome Copy.State α → Prop
  | .done a γ => P a ∧ State.Typed D γ Γ η
  | .raised e γ => (∃ F ∈ X.raises, Value.Typed D e F) ∧ State.Typed D γ Γ η
  | .jumped j γ => X.jumps j ∧ State.Typed D γ Γ η
  | .panicked _ γ => State.Typed D γ Γ η
  | .performed op v γ k =>
    (∃ τ ρ, X.performs op τ ρ ∧ Value.Typed D v τ ∧
      ∀ w x, Value.Typed D w ρ → World.Typed D x → (k w x).Ok D Γ η X P) ∧ State.Typed D γ Γ η
  | .outOfFuel => True
  | .stuck => False

/-- A sound outcome's step after it, sound on each value: a performance's
rest is still sound after it. -/
theorem Outcome.Ok.bind {Γ : Ctx} {η : REnv} {X : Exits} {P : α → Prop} {Q : β → Prop}
    {f : α → Copy.State → Outcome Copy.State β}
    (hf : ∀ a γ, P a → State.Typed D γ Γ η → (f a γ).Ok D Γ η X Q) :
    ∀ {o : Outcome Copy.State α}, o.Ok D Γ η X P → (o.bind f).Ok D Γ η X Q
  | .done a γ, ⟨ha, hγ⟩ => hf a γ ha hγ
  | .raised _ _, h => h
  | .jumped _ _, h => h
  | .panicked _ _, h => h
  | .performed _ _ _ _, ⟨⟨τ, ρ, hop, hv, hk⟩, hγ⟩ =>
    ⟨⟨τ, ρ, hop, hv, fun w x hw hx => Outcome.Ok.bind hf (hk w x hw hx)⟩, hγ⟩
  | .outOfFuel, h => h
  | .stuck, h => h

/-- A step that ends soundly from every frame of `Γ` (values.inout-arguments: copy-in,
copy-out, the reference interpreter's model). -/
def Eval.Ok (D : Decls) (Γ : Ctx) (η : REnv) (X : Exits) (P : α → Prop)
    (m : Eval Copy.State α) : Prop :=
  ∀ γ, State.Typed D γ Γ η → (m γ).Ok D Γ η X P

namespace Eval.Ok

variable {Γ : Ctx} {η : REnv} {X : Exits} {P : α → Prop} {Q : β → Prop}

/-- Every raise of `X` is one of `X'`. -/
def _root_.Stilt.Exits.Raises (D : Decls) (X X' : Exits) : Prop :=
  ∀ e, ∀ F ∈ X.raises, Value.Typed D e F → ∃ F' ∈ X'.raises, Value.Typed D e F'

theorem pure {a : α} (h : P a) : Eval.Ok D Γ η X P (Eval.pure a) := fun _ hγ => ⟨h, hγ⟩

theorem bind {m : Eval Copy.State α} {f : α → Eval Copy.State β} (hm : Eval.Ok D Γ η X P m)
    (hf : ∀ a, P a → Eval.Ok D Γ η X Q (f a)) : Eval.Ok D Γ η X Q (m >>= f) := fun γ hγ =>
  (hm γ hγ).bind fun a γ' ha hγ' => hf a ha γ' hγ'

/-- Every performance of `X` is one of `X'`, at the same types. -/
def _root_.Stilt.Exits.Performs (X X' : Exits) : Prop :=
  ∀ op τ ρ, X.performs op τ ρ → X'.performs op τ ρ

theorem _root_.Stilt.Outcome.Ok.mono {P' : α → Prop} {X' : Exits} (hP : ∀ a, P a → P' a)
    (hR : X.Raises D X') (hJ : ∀ j, X.jumps j → X'.jumps j) (hO : X.Performs X') :
    ∀ {o : Outcome Copy.State α}, o.Ok D Γ η X P → o.Ok D Γ η X' P'
  | .done a _, ⟨ha, h⟩ => ⟨hP a ha, h⟩
  | .raised e _, ⟨⟨F, hF, he⟩, h⟩ => ⟨hR e F hF he, h⟩
  | .jumped j _, ⟨hj, h⟩ => ⟨hJ j hj, h⟩
  | .panicked _ _, h => h
  | .performed op _ _ _, ⟨⟨τ, ρ, hop, hv, hk⟩, h⟩ =>
    ⟨⟨τ, ρ, hO op _ _ hop, hv, fun w x hw hx => Outcome.Ok.mono hP hR hJ hO (hk w x hw hx)⟩, h⟩
  | .outOfFuel, h => h
  | .stuck, h => h

theorem mono {m : Eval Copy.State α} {P' : α → Prop} {X' : Exits} (hm : Eval.Ok D Γ η X P m)
    (hP : ∀ a, P a → P' a) (hR : X.Raises D X') (hJ : ∀ j, X.jumps j → X'.jumps j)
    (hO : X.Performs X' := by intro _ _ _ h; exact h) :
    Eval.Ok D Γ η X' P' m := fun γ hγ => (hm γ hγ).mono hP hR hJ hO

theorem outOfFuel : Eval.Ok D Γ η X P (Eval.outOfFuel : Eval Copy.State α) := fun _ _ => trivial

theorem throw {e : Value} {F : STy} (hF : F ∈ X.raises) (he : Value.Typed D e F) :
    Eval.Ok D Γ η X P (Eval.throw e : Eval Copy.State α) := fun _ hγ => ⟨⟨F, hF, he⟩, hγ⟩

theorem jump {j : Jump} (hj : X.jumps j) : Eval.Ok D Γ η X P (Eval.jump j : Eval Copy.State α) :=
  fun _ hγ => ⟨hj, hγ⟩

theorem _root_.Stilt.Outcome.Ok.turn {X' : Exits} {P : Value → Prop} (hR : X.Raises D X')
    (hret : ∀ v, X.jumps (.ret v) → X'.jumps (.ret v)) (hO : X.Performs X') :
    ∀ {o : Outcome Copy.State Value}, o.Ok D Γ η X P →
      o.turn.Ok D Γ η X' (fun g => g = false → X.jumps .brk)
  | .done _ _, ⟨_, h⟩ => ⟨(nomatch ·), h⟩
  | .jumped .brk _, ⟨hj, h⟩ => ⟨fun _ => hj, h⟩
  | .jumped .cont _, ⟨_, h⟩ => ⟨(nomatch ·), h⟩
  | .jumped (.ret v) _, ⟨hj, h⟩ => ⟨hret v hj, h⟩
  | .raised e _, ⟨⟨F, hF, he⟩, h⟩ => ⟨hR e F hF he, h⟩
  | .panicked _ _, h => h
  | .performed op _ _ _, ⟨⟨τ, ρ, hop, hv, hk⟩, h⟩ =>
    ⟨⟨τ, ρ, hO op _ _ hop, hv, fun w x hw hx => Outcome.Ok.turn hR hret hO (hk w x hw hx)⟩, h⟩
  | .outOfFuel, h => h
  | .stuck, h => h

/-- A turn of a loop's body ends soundly, with `false` only when the body
broke out, which its exits allow (expressions.break-and-continue). -/
theorem turn {m : Eval Copy.State Value} {X' : Exits} {P : Value → Prop} (hm : Eval.Ok D Γ η X P m)
    (hR : X.Raises D X') (hret : ∀ v, X.jumps (.ret v) → X'.jumps (.ret v))
    (hO : X.Performs X' := by intro _ _ _ h; exact h) :
    Eval.Ok D Γ η X' (fun g => g = false → X.jumps .brk) (Eval.turn m) := fun γ hγ =>
  (hm γ hγ).turn hR hret hO

/-- A read that reaches a value the property holds of, or panics. -/
theorem ofExcept {x : Except Fault α}
    (h : (∃ a, x = .ok a ∧ P a) ∨ x = .error (.panic .bounds)) :
    Eval.Ok D Γ η X P (Eval.ofExcept x) := by
  intro γ hγ
  rcases h with ⟨a, rfl, ha⟩ | rfl
  · exact ⟨ha, hγ⟩
  · exact hγ

theorem inspect {f : Copy.State → Except Fault α}
    (h : ∀ γ, State.Typed D γ Γ η → (∃ a, f γ = .ok a ∧ P a) ∨ f γ = .error (.panic .bounds)) :
    Eval.Ok D Γ η X P (Eval.inspect f) := fun γ hγ => ofExcept (h γ hγ) γ hγ

theorem update {f : Copy.State → Except Fault Copy.State}
    (h : ∀ γ, State.Typed D γ Γ η →
      (∃ γ', f γ = .ok γ' ∧ State.Typed D γ' Γ η) ∨ f γ = .error (.panic .bounds)) :
    Eval.Ok D Γ η X (fun _ => True) (Eval.update f) := by
  intro γ hγ
  unfold Eval.update
  rcases h γ hγ with ⟨γ', h', hγ'⟩ | h' <;> rw [h']
  · exact ⟨trivial, hγ'⟩
  · exact hγ

/-- An outcome of a scope with one more binding, the scope ended
(expressions.scope). -/
theorem _root_.Stilt.Outcome.Ok.unbind {x : Name} {b : Binding} :
    ∀ {o : Outcome Copy.State α}, o.Ok D ((x, b) :: Γ) η X P → (o.unbind Copy.memory).Ok D Γ η X P
  | .done _ (_, _), ⟨ha, .cons _ hrest, hw⟩ => ⟨ha, hrest, hw⟩
  | .raised _ (_, _), ⟨he, .cons _ hrest, hw⟩ => ⟨he, hrest, hw⟩
  | .jumped _ (_, _), ⟨hj, .cons _ hrest, hw⟩ => ⟨hj, hrest, hw⟩
  | .panicked _ (_, _), ⟨.cons _ hrest, hw⟩ => ⟨hrest, hw⟩
  | .performed _ _ (_, _) _, ⟨⟨τ, ρ, hop, hv, hk⟩, .cons _ hrest, hw⟩ =>
    ⟨⟨τ, ρ, hop, hv, fun w x hw hx => Outcome.Ok.unbind (hk w x hw hx)⟩, hrest, hw⟩
  | .outOfFuel, h => h
  | .stuck, h => h

/-- A step in a scope with one more binding, which it ends however the step
ends (expressions.scope). -/
theorem withVar {x : Name} {v : Value} {b : Binding} {m : Eval Copy.State α}
    (hv : Value.Typed D v (b.type.close η)) (hm : Eval.Ok D ((x, b) :: Γ) η X P m) :
    Eval.Ok D Γ η X P (Eval.withVar Copy.memory x v m) := fun γ hγ =>
  (hm ((x, v) :: γ.1, γ.2) ⟨Frame.Typed.cons hv hγ.1, hγ.2⟩).unbind

theorem _root_.Stilt.Outcome.Ok.handle {h : Value → Copy.State → Outcome Copy.State α}
    {X₀ : Exits}
    (hh : ∀ e γ, ∀ F ∈ X₀.raises, Value.Typed D e F → State.Typed D γ Γ η → (h e γ).Ok D Γ η X P)
    (hJ : ∀ j, X₀.jumps j → X.jumps j) (hO : X₀.Performs X) :
    ∀ {o : Outcome Copy.State α}, o.Ok D Γ η X₀ P → (o.handle h).Ok D Γ η X P
  | .done _ _, h' => h'
  | .raised e γ, ⟨⟨F, hF, he⟩, h'⟩ => hh e γ F hF he h'
  | .jumped j _, ⟨hj, h'⟩ => ⟨hJ j hj, h'⟩
  | .panicked _ _, h' => h'
  | .performed op _ _ _, ⟨⟨τ, ρ, hop, hv, hk⟩, h'⟩ =>
    ⟨⟨τ, ρ, hO op _ _ hop, hv, fun w x hw hx => Outcome.Ok.handle hh hJ hO (hk w x hw hx)⟩, h'⟩
  | .outOfFuel, h' => h'
  | .stuck, h' => h'

theorem handle {m : Eval Copy.State α} {h : Value → Eval Copy.State α} {X₀ : Exits}
    (hm : Eval.Ok D Γ η X₀ P m)
    (hh : ∀ e, ∀ F ∈ X₀.raises, Value.Typed D e F → Eval.Ok D Γ η X P (h e))
    (hJ : ∀ j, X₀.jumps j → X.jumps j)
    (hO : X₀.Performs X := by intro _ _ _ h; exact h) :
    Eval.Ok D Γ η X P (Eval.handle m h) := fun γ hγ =>
  (hm γ hγ).handle (fun e γ' F hF he hγ' => hh e F hF he γ' hγ') hJ hO

end Eval.Ok

end

end Stilt
