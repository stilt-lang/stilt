import Stilt.Soundness.Theorem
import Stilt.Handling.Sound

/-!
# Outcomes that keep the world's output and input

`Outcome.KeepsIo D X c o`: every state that `o` carries has the output, the standard error and
the input `c`, and the rest of each performance, resumed in a typed world with a value of
each type its operation may give, keeps that world's. What the code around a performance runs
before resuming it, the handler's body, is not the code's own. `Eval.KeepsIo` asks it of a step
from every typed state of its context, from the world it starts in.

A step that only reads and writes frames keeps it, and so do the steps around it when what
they run keeps it: a step after another runs from a state that type soundness types
(`Outcome.Ok`), so the lemmas that run a second step take the first's `Ok` too.
-/

namespace Stilt

/-- The parts of a world that `io` reads and writes: its output, its standard error and the
input not read yet (std.io). -/
def World.io (w : World) : String × String × String := (w.out, w.err, w.input)

section

variable {D : Decls} {α β : Type}

/-- Every state `o` carries has the output, standard error and input `c`; a performance's
rest, resumed in a typed world with a value of each type its operation may give at `X`, keeps
that world's. -/
def Outcome.KeepsIo (D : Decls) (X : Exits) (c : String × String × String) :
    Outcome Copy.State α → Prop
  | .done _ s => s.2.io = c
  | .raised _ s => s.2.io = c
  | .jumped _ s => s.2.io = c
  | .panicked _ s => s.2.io = c
  | .performed op v s k => s.2.io = c ∧ ∀ w x, World.Typed D x →
      (∀ τ ρ, X.performs op τ ρ → Value.Typed D v τ → Value.Typed D w ρ) →
      Outcome.KeepsIo D X x.io (k w x)
  | .outOfFuel => True
  | .stuck => True

/-- From every typed state of `Γ`, `m` keeps the output, standard error and input of the
world it starts in. -/
def Eval.KeepsIo (D : Decls) (Γ : Ctx) (η : REnv) (X : Exits) (m : Eval Copy.State α) : Prop :=
  ∀ γ, State.Typed D γ Γ η → (m γ).KeepsIo D X γ.2.io

variable {Γ : Ctx} {η : REnv} {X : Exits} {P : α → Prop}

namespace Outcome.KeepsIo

/-- A step after an outcome keeps the world when the outcome does, and the step does from
each typed state the outcome ends in. -/
theorem bind {f : α → Copy.State → Outcome Copy.State β}
    (hf : ∀ a γ, P a → State.Typed D γ Γ η → (f a γ).KeepsIo D X γ.2.io) :
    ∀ {o : Outcome Copy.State α} {c}, o.Ok D Γ η X P → o.KeepsIo D X c → (o.bind f).KeepsIo D X c
  | .done a γ, _, ⟨ha, hγ⟩, hk => hk ▸ hf a γ ha hγ
  | .raised _ _, _, _, hk => hk
  | .jumped _ _, _, _, hk => hk
  | .panicked _ _, _, _, hk => hk
  | .performed _ _ _ _, _, ⟨⟨τ, ρ, hop, hv, hok⟩, _⟩, ⟨hc, hk⟩ =>
    ⟨hc, fun w x hx hw => Outcome.KeepsIo.bind hf (hok w x (hw τ ρ hop hv) hx) (hk w x hx hw)⟩
  | .outOfFuel, _, _, _ => trivial
  | .stuck, _, _, _ => trivial

/-- A step after an outcome keeps the world when the outcome does, and the step does from
every state. -/
theorem bindAny {f : α → Copy.State → Outcome Copy.State β} (hf : ∀ a γ, (f a γ).KeepsIo D X γ.2.io) :
    ∀ {o : Outcome Copy.State α} {c}, o.KeepsIo D X c → (o.bind f).KeepsIo D X c
  | .done a γ, _, hk => hk ▸ hf a γ
  | .raised _ _, _, hk | .jumped _ _, _, hk | .panicked _ _, _, hk => hk
  | .performed _ _ _ _, _, ⟨hc, hk⟩ =>
    ⟨hc, fun w x hx hw => Outcome.KeepsIo.bindAny hf (hk w x hx hw)⟩
  | .outOfFuel, _, _ | .stuck, _, _ => trivial

/-- Exits that perform more ask more of the values that resume a rest. -/
theorem mono {X' : Exits} (hO : X.Performs X') :
    ∀ {o : Outcome Copy.State α} {c}, o.KeepsIo D X c → o.KeepsIo D X' c
  | .done _ _, _, h | .raised _ _, _, h | .jumped _ _, _, h | .panicked _ _, _, h => h
  | .performed _ _ _ _, _, ⟨hc, hk⟩ =>
    ⟨hc, fun w x hx hw => Outcome.KeepsIo.mono hO (hk w x hx fun τ ρ h hv => hw τ ρ (hO _ _ _ h) hv)⟩
  | .outOfFuel, _, h | .stuck, _, h => h

/-- A loop body's outcome as its turn's keeps what the body kept. -/
theorem turn : ∀ {o : Outcome Copy.State Value} {c}, o.KeepsIo D X c → o.turn.KeepsIo D X c
  | .done _ _, _, h | .raised _ _, _, h | .panicked _ _, _, h => h
  | .jumped .brk _, _, h | .jumped .cont _, _, h | .jumped (.ret _) _, _, h => h
  | .performed _ _ _ _, _, ⟨hc, hk⟩ => ⟨hc, fun w x hx hw => Outcome.KeepsIo.turn (hk w x hx hw)⟩
  | .outOfFuel, _, h | .stuck, _, h => h

/-- An outcome with its raise handed to a handler keeps the world when the handler does,
from the raise's state, on an error that the exits allow. -/
theorem handle {h : Value → Copy.State → Outcome Copy.State α} {X₀ : Exits}
    (hh : ∀ e γ, ∀ F ∈ X₀.raises, Value.Typed D e F → State.Typed D γ Γ η →
      (h e γ).KeepsIo D X γ.2.io) (hO : X₀.Performs X) :
    ∀ {o : Outcome Copy.State α} {c}, o.Ok D Γ η X₀ P → o.KeepsIo D X₀ c →
      (o.handle h).KeepsIo D X c
  | .done _ _, _, _, hk | .jumped _ _, _, _, hk | .panicked _ _, _, _, hk => hk
  | .raised e γ, _, ⟨⟨F, hF, he⟩, hγ⟩, hk => hk ▸ hh e γ F hF he hγ
  | .performed _ _ _ _, _, ⟨⟨τ, ρ, hop, hv, hok⟩, _⟩, ⟨hc, hk⟩ =>
    ⟨hc, fun w x hx hw => Outcome.KeepsIo.handle hh hO (hok w x (hw τ ρ (hO _ _ _ hop) hv) hx)
      (hk w x hx fun τ' ρ' h hv' => hw τ' ρ' (hO _ _ _ h) hv')⟩
  | .outOfFuel, _, _, hk | .stuck, _, _, hk => hk

/-- An outcome of a scope, the scope ended, keeps what it kept: ending a scope changes the
frame alone. -/
theorem unbind : ∀ {o : Outcome Copy.State α} {c}, o.KeepsIo D X c → (o.unbind Copy.memory).KeepsIo D X c
  | .done _ (_, _), _, h | .raised _ (_, _), _, h | .jumped _ (_, _), _, h
  | .panicked _ (_, _), _, h => h
  | .performed _ _ (_, _) _, _, ⟨hc, hk⟩ =>
    ⟨hc, fun w x hx hw => Outcome.KeepsIo.unbind (hk w x hx hw)⟩
  | .outOfFuel, _, h | .stuck, _, h => h

end Outcome.KeepsIo

/-- `Outcome.KeepsIo.bind` from the outcome's soundness. -/
theorem Outcome.Ok.keeps_bind {f : α → Copy.State → Outcome Copy.State β}
    {o : Outcome Copy.State α} {c} (ho : o.Ok D Γ η X P)
    (hf : ∀ a γ, P a → State.Typed D γ Γ η → (f a γ).KeepsIo D X γ.2.io) (hk : o.KeepsIo D X c) :
    (o.bind f).KeepsIo D X c :=
  Outcome.KeepsIo.bind hf ho hk

/-- `Outcome.KeepsIo.handle` with its arguments in the order of `Eval.KeepsIo.handle`. -/
theorem Outcome.KeepsIo.handle' {h : Value → Copy.State → Outcome Copy.State α} {X₀ : Exits}
    {o : Outcome Copy.State α} {c} (hk : o.KeepsIo D X₀ c)
    (hh : ∀ e γ, ∀ F ∈ X₀.raises, Value.Typed D e F → State.Typed D γ Γ η →
      (h e γ).KeepsIo D X γ.2.io) (hO : X₀.Performs X) (ho : o.Ok D Γ η X₀ P) :
    (o.handle h).KeepsIo D X c :=
  Outcome.KeepsIo.handle hh hO ho hk

namespace Eval.KeepsIo

theorem bind {m : Eval Copy.State α} {f : α → Eval Copy.State β} (hm : Eval.Ok D Γ η X P m)
    (hk : Eval.KeepsIo D Γ η X m) (hf : ∀ a, P a → Eval.KeepsIo D Γ η X (f a)) :
    Eval.KeepsIo D Γ η X (m >>= f) := fun γ hγ =>
  (hm γ hγ).keeps_bind (fun a γ' ha hγ' => hf a ha γ' hγ') (hk γ hγ)

theorem pure {a : α} : Eval.KeepsIo D Γ η X (Eval.pure a : Eval Copy.State α) := fun _ _ => rfl

theorem mono {m : Eval Copy.State α} {X' : Exits} (hk : Eval.KeepsIo D Γ η X m)
    (hO : X.Performs X' := by intro _ _ _ h; exact h) : Eval.KeepsIo D Γ η X' m := fun γ hγ =>
  (hk γ hγ).mono hO

theorem outOfFuel : Eval.KeepsIo D Γ η X (Eval.outOfFuel : Eval Copy.State α) := fun _ _ => trivial

theorem throw {e : Value} : Eval.KeepsIo D Γ η X (Eval.throw e : Eval Copy.State α) :=
  fun _ _ => rfl

theorem jump {j : Jump} : Eval.KeepsIo D Γ η X (Eval.jump j : Eval Copy.State α) := fun _ _ => rfl

theorem fail {f : Fault} : Eval.KeepsIo D Γ η X (Eval.fail f : Eval Copy.State α) := fun _ _ => by
  cases f <;> first | rfl | trivial

theorem ofExcept {x : Except Fault α} : Eval.KeepsIo D Γ η X (Eval.ofExcept x) := fun _ _ => by
  cases x with
  | ok => rfl
  | error f => cases f <;> first | rfl | trivial

theorem inspect {f : Copy.State → Except Fault α} : Eval.KeepsIo D Γ η X (Eval.inspect f) :=
  fun γ hγ => ofExcept γ hγ

/-- A step that changes the frame alone keeps the world. -/
theorem update {f : Copy.State → Except Fault Copy.State}
    (h : ∀ γ γ', f γ = .ok γ' → γ'.2 = γ.2) : Eval.KeepsIo D Γ η X (Eval.update f) := by
  intro γ _
  unfold Eval.update
  cases hf : f γ with
  | ok γ' => exact congrArg World.io (h γ γ' hf)
  | error e => cases e <;> first | rfl | trivial

theorem turn {m : Eval Copy.State Value} (hk : Eval.KeepsIo D Γ η X m) :
    Eval.KeepsIo D Γ η X (Eval.turn m) := fun γ hγ => (hk γ hγ).turn

theorem handle {m : Eval Copy.State α} {h : Value → Eval Copy.State α} {X₀ : Exits}
    (hm : Eval.Ok D Γ η X₀ P m) (hk : Eval.KeepsIo D Γ η X₀ m)
    (hh : ∀ e, ∀ F ∈ X₀.raises, Value.Typed D e F → Eval.KeepsIo D Γ η X (h e))
    (hO : X₀.Performs X := by intro _ _ _ h; exact h) :
    Eval.KeepsIo D Γ η X (Eval.handle m h) := fun γ hγ =>
  (hk γ hγ).handle' (fun e γ' F hF he hγ' => hh e F hF he γ' hγ') hO (hm γ hγ)

/-- A step in a scope with one more binding keeps the world when the step does. -/
theorem withVar {x : Name} {v : Value} {b : Binding} {m : Eval Copy.State α}
    (hv : Value.Typed D v (b.type.close η)) (hm : Eval.KeepsIo D ((x, b) :: Γ) η X m) :
    Eval.KeepsIo D Γ η X (Eval.withVar Copy.memory x v m) := fun γ hγ =>
  (hm ((x, v) :: γ.1, γ.2) ⟨Frame.Typed.cons hv hγ.1, hγ.2⟩).unbind

/-- A step after one that keeps the world keeps it when the step does from every state. -/
theorem bindAny {m : Eval Copy.State α} {f : α → Eval Copy.State β} (hk : Eval.KeepsIo D Γ η X m)
    (hf : ∀ a γ, (f a γ).KeepsIo D X γ.2.io) : Eval.KeepsIo D Γ η X (m >>= f) := fun γ hγ =>
  Outcome.KeepsIo.bindAny hf (hk γ hγ)

/-- A read of the state, then a step from it, keeps the world when the step does. -/
theorem inspect_bind {f : Copy.State → Except Fault α} {g : α → Eval Copy.State β}
    (hg : ∀ a, Eval.KeepsIo D Γ η X (g a)) : Eval.KeepsIo D Γ η X (Eval.inspect f >>= g) := by
  intro γ hγ
  show ((Eval.inspect f γ).bind fun a s => g a s).KeepsIo D X γ.2.io
  unfold Eval.inspect Eval.ofExcept
  cases f γ with
  | ok a => exact hg a γ hγ
  | error e => cases e <;> first | rfl | trivial

/-- A performance keeps the world it leaves, and its rest the world it resumes in. -/
theorem perform {op : Operation} {v : Value} :
    Eval.KeepsIo D Γ η X (Eval.perform Copy.memory op v) := fun ⟨_, _⟩ _ =>
  ⟨rfl, fun _ _ _ _ => rfl⟩

end Eval.KeepsIo

/-- The steps that only read a value, or build one, keep the world from every state. -/
theorem Outcome.KeepsIo.pure_any {a : α} {γ : Copy.State} :
    (Eval.pure a γ : Outcome Copy.State α).KeepsIo D X γ.2.io := rfl

theorem Outcome.KeepsIo.fail_any {f : Fault} {γ : Copy.State} :
    (Eval.fail f γ : Outcome Copy.State α).KeepsIo D X γ.2.io := by
  cases f <;> first | rfl | trivial

theorem Outcome.KeepsIo.ofExcept_any {x : Except Fault α} {γ : Copy.State} :
    (Eval.ofExcept x γ).KeepsIo D X γ.2.io := by
  cases x with
  | ok => rfl
  | error f => cases f <;> first | rfl | trivial

theorem Outcome.KeepsIo.asInt {v : Value} {γ : Copy.State} :
    (Eval.asInt v γ : Outcome Copy.State Int).KeepsIo D X γ.2.io := by
  cases v <;> first | rfl | trivial

theorem Outcome.KeepsIo.asBool {v : Value} {γ : Copy.State} :
    (Eval.asBool v γ : Outcome Copy.State Bool).KeepsIo D X γ.2.io := by
  cases v <;> first | rfl | trivial

theorem Outcome.KeepsIo.asList {v : Value} {γ : Copy.State} :
    (Eval.asList v γ : Outcome Copy.State (List Value)).KeepsIo D X γ.2.io := by
  cases v <;> first | rfl | trivial

theorem Outcome.KeepsIo.declare {R : Name} {written : List (Name × Value)} {γ : Copy.State} :
    (Eval.declare D R written γ : Outcome Copy.State Value).KeepsIo D X γ.2.io := by
  cases h : D.record? R with
  | none => simp only [Eval.declare, h]; exact Outcome.KeepsIo.fail_any
  | some r =>
    cases h₂ : r.fields.mapM (fun (f, _) => (written.lookup f).map (f, ·)) with
    | none => simp only [Eval.declare, h, h₂]; exact Outcome.KeepsIo.fail_any
    | some _ => simp only [Eval.declare, h, h₂]; rfl

theorem Outcome.KeepsIo.method {t m : Name} {τ : Ty} {γ : Copy.State} :
    (Eval.method D t m τ γ : Outcome Copy.State Value).KeepsIo D X γ.2.io := by
  cases h : τ.head? with
  | none => simp only [Eval.method, h]; exact Outcome.KeepsIo.fail_any
  | some hd =>
    cases h₂ : D.traitImpl? t hd with
    | none => simp only [Eval.method, h, h₂]; exact Outcome.KeepsIo.fail_any
    | some _ => simp only [Eval.method, h, h₂]; rfl

end

end Stilt
