import Stilt.Held.World
import Stilt.Semantics

/-!
# Outcomes that keep a cell held

An outcome keeps the cell a handle names held when every state it carries holds it, and
every rest of a performance, resumed in a world that holds it, again ends so
(`Outcome.KeepsHeld`): no code but the `when` holding a cell lets go of it, so none reads
or writes its value but through the `when`'s names (shared.when). Each state's world also
extends the one the evaluation started in: cells are made and never unmade, so a handle
names the same cell throughout.

This module proves it of what a run is made of: binding and ending scopes, calls,
handlers, the `when` that puts values back in the cells it holds, none of them the cell
held before it started, and the `with` that lets go of the cells held since it started.
-/

namespace Stilt

variable {τ α β : Type}

/-- Every state `o` carries holds the cell `k` names, in a world that extends `b`, and
every rest of a performance in it, resumed in a world that extends the performance's and
holds `k`, again ends so from that world. -/
def Outcome.KeepsHeld (k : Ty × Nat) (b : World) : Outcome (τ × World) α → Prop
  | .done _ s | .raised _ s | .jumped _ s | .panicked _ s => b.Extends s.2 ∧ s.2.Held k
  | .performed _ _ s r =>
    b.Extends s.2 ∧ s.2.Held k ∧ ∀ v w, s.2.Extends w → w.Held k → (r v w).KeepsHeld k w
  | .outOfFuel | .stuck => True

/-- From every state whose world holds `k`, `m` keeps it held. -/
def Eval.KeepsHeld (k : Ty × Nat) (m : Eval (τ × World) α) : Prop :=
  ∀ s, s.2.Held k → (m s).KeepsHeld k s.2

namespace Outcome.KeepsHeld

variable {k : Ty × Nat}

/-- What an outcome keeps from a later world, it keeps from an earlier one. -/
theorem base {a b : World} (hab : a.Extends b) :
    ∀ {o : Outcome (τ × World) α}, o.KeepsHeld k b → o.KeepsHeld k a
  | .done _ _, ⟨h₁, h₂⟩ | .raised _ _, ⟨h₁, h₂⟩ | .jumped _ _, ⟨h₁, h₂⟩
  | .panicked _ _, ⟨h₁, h₂⟩ => ⟨hab.trans h₁, h₂⟩
  | .performed _ _ _ _, ⟨h₁, h₂, h₃⟩ => ⟨hab.trans h₁, h₂, h₃⟩
  | .outOfFuel, _ | .stuck, _ => trivial

theorem fault (f : Fault) {b : World} {s : τ × World} (hb : b.Extends s.2) (hk : s.2.Held k) :
    (Outcome.fault f s : Outcome (τ × World) α).KeepsHeld k b := by
  cases f
  · exact ⟨hb, hk⟩
  · trivial

theorem bind {f : α → τ × World → Outcome (τ × World) β} :
    ∀ {b : World} {o : Outcome (τ × World) α},
      (∀ a s, b.Extends s.2 → s.2.Held k → (f a s).KeepsHeld k s.2) →
      o.KeepsHeld k b → (o.bind f).KeepsHeld k b
  | _, .done a s, hf, ⟨h₁, h₂⟩ => base h₁ (hf a s h₁ h₂)
  | _, .raised _ _, _, h | _, .jumped _ _, _, h | _, .panicked _ _, _, h => h
  | _, .performed _ _ _ _, hf, ⟨h₁, h₂, h₃⟩ =>
    ⟨h₁, h₂, fun v w hw hk => bind (fun a s hs hk' => hf a s (h₁.trans (hw.trans hs)) hk') (h₃ v w hw hk)⟩
  | _, .outOfFuel, _, _ | _, .stuck, _, _ => trivial

theorem handle {g : Value → τ × World → Outcome (τ × World) α} :
    ∀ {b : World} {o : Outcome (τ × World) α},
      (∀ e s, b.Extends s.2 → s.2.Held k → (g e s).KeepsHeld k s.2) →
      o.KeepsHeld k b → (o.handle g).KeepsHeld k b
  | _, .raised e s, hg, ⟨h₁, h₂⟩ => base h₁ (hg e s h₁ h₂)
  | _, .done _ _, _, h | _, .jumped _ _, _, h | _, .panicked _ _, _, h => h
  | _, .performed _ _ _ _, hg, ⟨h₁, h₂, h₃⟩ =>
    ⟨h₁, h₂, fun v w hw hk => handle (fun e s hs hk' => hg e s (h₁.trans (hw.trans hs)) hk') (h₃ v w hw hk)⟩
  | _, .outOfFuel, _, _ | _, .stuck, _, _ => trivial

theorem turn : ∀ {b : World} {o : Outcome (τ × World) Value}, o.KeepsHeld k b → o.turn.KeepsHeld k b
  | _, .done _ _, h | _, .raised _ _, h | _, .panicked _ _, h => h
  | _, .jumped .brk _, h | _, .jumped .cont _, h | _, .jumped (.ret _) _, h => h
  | _, .performed _ _ _ _, ⟨h₁, h₂, h₃⟩ => ⟨h₁, h₂, fun v w hw hk => turn (h₃ v w hw hk)⟩
  | _, .outOfFuel, _ | _, .stuck, _ => trivial

variable (F : Frames τ)

theorem unbind : ∀ {b : World} {o : Outcome (τ × World) α},
    o.KeepsHeld k b → (o.unbind F.withWorld).KeepsHeld k b
  | _, .done _ (_, _), h | _, .raised _ (_, _), h | _, .jumped _ (_, _), h
  | _, .panicked _ (_, _), h => h
  | _, .performed _ _ (_, _) _, ⟨h₁, h₂, h₃⟩ => ⟨h₁, h₂, fun v w hw hk => unbind (h₃ v w hw hk)⟩
  | _, .outOfFuel, _ | _, .stuck, _ => trivial

/-- A handler's outcome on the frames of the block keeps what it keeps of the world. -/
theorem lift (s : τ × World) : ∀ {b : World} {o : Outcome (τ × World) α},
    o.KeepsHeld k b → (o.lift F.withWorld s).KeepsHeld k b
  | _, .done _ _, h | _, .raised _ _, h | _, .jumped _ _, h | _, .panicked _ _, h => h
  | _, .performed _ _ _ _, ⟨h₁, h₂, h₃⟩ => ⟨h₁, h₂, fun v w hw hk => lift s (h₃ v w hw hk)⟩
  | _, .outOfFuel, _ | _, .stuck, _ => trivial

/-- Leaving a call keeps the world its callee left. -/
theorem leaveCall (bound : List (Name × Passed)) (s : τ × World) :
    ∀ {b : World} {o : Outcome (τ × World) Value},
      o.KeepsHeld k b → (o.leaveCall F.withWorld bound s).KeepsHeld k b
  | _, .done _ s', ⟨h₁, h₂⟩ | _, .raised _ s', ⟨h₁, h₂⟩ | _, .jumped (.ret _) s', ⟨h₁, h₂⟩
  | _, .panicked _ s', ⟨h₁, h₂⟩ => by
    simp only [Outcome.leaveCall, Frames.withWorld_leave]
    cases F.leave s.1 s'.1 bound with
    | ok _ => exact ⟨h₁, h₂⟩
    | error f => exact fault f (s := (s.1, s'.2)) h₁ h₂
  | _, .jumped .brk _, _ | _, .jumped .cont _, _ => trivial
  | _, .performed _ _ s' _, ⟨h₁, h₂, h₃⟩ => by
    simp only [Outcome.leaveCall, Frames.withWorld_leave]
    cases F.leave s.1 s'.1 bound with
    | ok _ => exact ⟨h₁, h₂, fun v w hw hk => leaveCall bound s (h₃ v w hw hk)⟩
    | error f => exact fault f (s := (s.1, s'.2)) h₁ h₂
  | _, .outOfFuel, _ | _, .stuck, _ => trivial

/-- The body of a handler that takes control keeps a cell held when the rests it resumes do,
from any world that extends `b₀`. -/
theorem runBody {resume : Value → World → Outcome (τ × World) Value} {b₀ : World}
    (hr : ∀ u x, b₀.Extends x → x.Held k → (resume u x).KeepsHeld k x) :
    ∀ {b : World} {o : Outcome (τ × World) Value}, b₀.Extends b → o.KeepsHeld k b →
      (o.runBody F.withWorld resume).KeepsHeld k b
  | _, .performed op u s r, hb, ⟨h₁, h₂, h₃⟩ => by
    unfold Outcome.runBody
    split
    · refine base h₁ (bind (fun a s' hs' hk' => ?_) (hr u s.2 (hb.trans h₁) h₂))
      exact lift F s' (runBody hr (hb.trans (h₁.trans hs')) (h₃ a s'.2 hs' hk'))
    · exact ⟨h₁, h₂, fun v w hw hk => runBody hr (hb.trans (h₁.trans hw)) (h₃ v w hw hk)⟩
  | _, .done _ _, _, h | _, .raised _ _, _, h | _, .jumped _ _, _, h | _, .panicked _ _, _, h => h
  | _, .outOfFuel, _, _ | _, .stuck, _, _ => trivial

/-- A `with` keeps a cell held when its block and its clauses do (handlers.with). -/
theorem handleWith {effect : Name} {control : Bool} {handler : Value}
    {call : Value → Value → τ × World → Outcome (τ × World) Value}
    (hcall : ∀ c v s, s.2.Held k → (call c v s).KeepsHeld k s.2) :
    ∀ {b : World} {o : Outcome (τ × World) Value}, o.KeepsHeld k b →
      (o.handleWith F.withWorld effect control handler call).KeepsHeld k b
  | _, .performed op v s r, ⟨h₁, h₂, h₃⟩ => by
    unfold Outcome.handleWith
    split
    · split
      · trivial
      · split
        · exact base h₁ (runBody F (b₀ := s.2) (fun u x hx hk => handleWith hcall (h₃ u x hx hk))
            (World.Extends.refl _) (hcall _ v s h₂))
        · exact base h₁ (bind (fun u s' hs' hk => handleWith hcall (h₃ u s'.2 hs' hk))
            (hcall _ v s h₂))
    · exact ⟨h₁, h₂, fun u w hw hk => handleWith hcall (h₃ u w hw hk)⟩
  | _, .done _ _, h | _, .raised _ _, h | _, .jumped _ _, h | _, .panicked _ _, h => h
  | _, .outOfFuel, _ | _, .stuck, _ => trivial

/-- A `with` that lets go of the cells held since it started keeps every cell held when it
started held. -/
theorem letGo {before : World} (hk : before.Held k) :
    ∀ {b : World} {o : Outcome (τ × World) α}, before.Extends b → o.KeepsHeld k b →
      (o.letGo F.withWorld before).KeepsHeld k b
  | _, .done _ (_, _), hb, ⟨h₁, h₂⟩ | _, .raised _ (_, _), hb, ⟨h₁, h₂⟩
  | _, .jumped _ (_, _), hb, ⟨h₁, h₂⟩ | _, .panicked _ (_, _), hb, ⟨h₁, h₂⟩ =>
    ⟨h₁.letGo before, World.Held.letGo (hb.trans h₁) hk h₂⟩
  | _, .performed _ _ _ _, hb, ⟨h₁, h₂, h₃⟩ =>
    ⟨h₁, h₂, fun v w hw hk' => letGo hk (hb.trans (h₁.trans hw)) (h₃ v w hw hk')⟩
  | _, .outOfFuel, _, _ | _, .stuck, _, _ => trivial

/-- Putting values back keeps every cell in its place, and every other cell held. -/
theorem putBack (held : Bool) : ∀ (cells : List (Name × Ty × Nat)) {s s' : τ × World},
    F.withWorld.putBack held cells s = .ok s' →
      s.2.Extends s'.2 ∧ ((∀ x c, (x, c) ∈ cells → c ≠ k) → s.2.Held k → s'.2.Held k)
  | [], _, _, h => by cases h; exact ⟨World.Extends.refl _, fun _ hk => hk⟩
  | (x, c) :: rest, (fr, w), s', h => by
    simp only [Memory.putBack] at h
    cases hr : F.withWorld.read (fr, w) x [] with
    | error e => rw [hr] at h; cases h
    | ok v =>
      rw [hr] at h
      obtain ⟨he, hk⟩ := putBack held rest (s := (fr, w.put c v held)) h
      refine ⟨(World.Extends.refl w |>.put c v held).trans he, fun hc hw => hk ?_ ?_⟩
      · exact fun y c' hm => hc y c' (List.mem_cons_of_mem _ hm)
      · exact hw.put (hc x c List.mem_cons_self) v held

theorem after {held : Bool} {cells : List (Name × Ty × Nat)} (hc : ∀ x c, (x, c) ∈ cells → c ≠ k)
    {b : World} {s : τ × World} {o : τ × World → Outcome (τ × World) α} (hb : b.Extends s.2)
    (hk : s.2.Held k) (ho : ∀ s', s.2.Extends s'.2 → s'.2.Held k → (o s').KeepsHeld k b) :
    (Outcome.after (F.withWorld.putBack held cells) s o).KeepsHeld k b := by
  unfold Outcome.after
  split
  · rename_i s' h
    obtain ⟨he, hk'⟩ := putBack F held cells h
    exact ho s' he (hk' hc hk)
  · exact fault _ hb hk

/-- A `when` that holds none of the cell `k` keeps it held when its block does: putting
its values back leaves `k`. -/
theorem release (cells : List (Name × Ty × Nat)) (hc : ∀ x c, (x, c) ∈ cells → c ≠ k) :
    ∀ {b : World} {o : Outcome (τ × World) α}, o.KeepsHeld k b →
      (o.release F.withWorld cells).KeepsHeld k b
  | _, .done _ _, ⟨h₁, h₂⟩ | _, .raised _ _, ⟨h₁, h₂⟩ | _, .jumped _ _, ⟨h₁, h₂⟩
  | _, .panicked _ _, ⟨h₁, h₂⟩ => after F hc h₁ h₂ fun _ he hk => ⟨h₁.trans he, hk⟩
  | _, .performed _ _ _ _, ⟨h₁, h₂, h₃⟩ => after F hc h₁ h₂ fun _ he hk =>
    ⟨h₁.trans he, hk, fun v w hw hk' => release cells hc (h₃ v w (he.trans hw) hk')⟩
  | _, .outOfFuel, _ | _, .stuck, _ => trivial

end Outcome.KeepsHeld

end Stilt
