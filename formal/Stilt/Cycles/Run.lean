import Stilt.Cycles.Chain
import Stilt.Soundness.Theorem

/-!
# The cycles of a run

The fundamental lemma keeps every world a well-typed program's run passes through typed: each
cell holds a value of its type (`World.Typed`). So the world a run ends in is typed, and
`on_cycle_can_reach_itself` holds of it: no cell of a `Shared<U>` whose `U` can't reach itself
is on a cycle there (cycles.can-form-cycle).
-/

namespace Stilt

/-- The world an outcome ends in, when it ends in a state. -/
def Outcome.world {σ α : Type} : Outcome (σ × World) α → Option World
  | .done _ s | .raised _ s | .jumped _ s | .panicked _ s | .performed _ _ s _ => some s.2
  | .outOfFuel | .stuck => none

/-- A sound outcome ends in a typed world. -/
theorem Outcome.Ok.world {D : Decls} {Γ : Ctx} {η : REnv} {X : Exits} {α : Type} {P : α → Prop} :
    ∀ {o : Outcome Copy.State α}, o.Ok D Γ η X P → ∀ w ∈ o.world, World.Typed D w
  | .done _ _, ⟨_, _, hw⟩, _, rfl => hw
  | .raised _ _, ⟨_, _, hw⟩, _, rfl => hw
  | .jumped _ _, ⟨_, _, hw⟩, _, rfl => hw
  | .panicked _ _, ⟨_, hw⟩, _, rfl => hw
  | .performed _ _ _ _, ⟨_, _, hw⟩, _, rfl => hw
  | .outOfFuel, _, _, h => nomatch h
  | .stuck, _, _, h => nomatch h

theorem Outcome.world_leaveBody {σ : Type} :
    ∀ (o : Outcome (σ × World) Value), ∀ w ∈ o.leaveBody.world, w ∈ o.world
  | .done _ _, _, h | .raised _ _, _, h | .panicked _ _, _, h => h
  | .jumped (.ret _) _, _, h | .jumped .brk _, _, h | .jumped .cont _, _, h => h
  | .performed _ _ _ _, _, h | .outOfFuel, _, h | .stuck, _, h => nomatch h

/-- A well-typed program's run, as the reference interpreter runs it, ends in a typed world. -/
theorem Program.WellTyped.world {p : Program} (hp : p.WellTyped) (fuel : Nat) (input : String) :
    ∀ w ∈ (p.runCopy fuel input).world, World.Typed p.decls w := by
  obtain ⟨_, hmain, _⟩ := hp.main
  have h := Decls.Typed.sound ⟨hp.decls, hp.typedIn.fns⟩ fuel hmain REnv.respects_closed []
  rw [Expr.substRows_nil] at h
  have ho := h ([], World.start input) ⟨.nil, fun _ h => nomatch h⟩
  exact fun w hw => ho.world w (Outcome.world_leaveBody _ w hw)

/-- cycles.can-form-cycle holds of the world a well-typed program's run ends in: a cell on
a cycle is one of a `Shared<U>` whose `U` can reach itself. -/
theorem Program.WellTyped.cycles {p : Program} (hp : p.WellTyped) (fuel : Nat) (input : String) :
    ∀ w ∈ (p.runCopy fuel input).world, ∀ (u : Ty) (k : Nat), w.Chain (u, k) (u, k) →
      CanReachItself p.decls u :=
  fun w hw _ _ hc => on_cycle_can_reach_itself (hp.world fuel input w hw) hc

end Stilt
