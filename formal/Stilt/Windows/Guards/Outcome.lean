import Stilt.Windows.Guards.Regions
import Stilt.Semantics

/-!
# Outcomes that evolve by allowed writes

`o.Within ok P s`: every state the in-place outcome `o` ends in evolved from `s` by writes
that `ok` allows (`EvolvesBy`), a value it ends with satisfies `P`, and each rest of a
performance, resumed with any value in any world, ends so again. These are the states that
the agreement of in-place mutation relates (`Stilt.InPlace.Steps`), the rests of
performances included.

Each step that passes an outcome on keeps it: the steps after a value, a handler of raises,
a turn of a loop, the end of a scope, a handler's body on the frames of the block, the end
of a `when` and of a `with`.
-/

namespace Stilt

variable {α β : Type}

open InPlace

/-- Every state that `o` ends in, a performance's rests included, evolved from `s` by
writes that `ok` allows, and every value it ends with satisfies `P`. -/
def Outcome.Within (ok : Path → Prop) (P : α → Prop) (s : State) :
    Outcome (State × World) α → Prop
  | .done a t => P a ∧ EvolvesBy ok s t.1
  | .raised _ t => EvolvesBy ok s t.1
  | .jumped _ t => EvolvesBy ok s t.1
  | .panicked _ t => EvolvesBy ok s t.1
  | .performed _ _ t k => EvolvesBy ok s t.1 ∧ ∀ w x, Outcome.Within ok P s (k w x)
  | .outOfFuel => True
  | .stuck => True

namespace Outcome.Within

variable {ok : Path → Prop} {P : α → Prop} {Q : β → Prop}

/-- What evolves from a later state evolves from an earlier one. -/
theorem base {s₀ s : State} (hv : Valid s₀) (h : EvolvesBy ok s₀ s) :
    ∀ {o : Outcome (State × World) α}, o.Within ok P s → o.Within ok P s₀
  | .done _ _, ⟨ha, h'⟩ => ⟨ha, h.trans hv h'⟩
  | .raised _ _, h' => h.trans hv h'
  | .jumped _ _, h' => h.trans hv h'
  | .panicked _ _, h' => h.trans hv h'
  | .performed _ _ _ _, ⟨h', hk⟩ => ⟨h.trans hv h', fun w x => base hv h (hk w x)⟩
  | .outOfFuel, _ => trivial
  | .stuck, _ => trivial

theorem mono {s₀ : State} {Q : α → Prop} (hPQ : ∀ a, P a → Q a) {ok' : Path → Prop} (hok : ∀ p, ok p → ok' p) :
    ∀ {o : Outcome (State × World) α}, o.Within ok P s₀ → o.Within ok' Q s₀
  | .done _ _, ⟨ha, h⟩ => ⟨hPQ _ ha, EvolvesBy.mono h hok⟩
  | .raised _ _, h => EvolvesBy.mono h hok
  | .jumped _ _, h => EvolvesBy.mono h hok
  | .panicked _ _, h => EvolvesBy.mono h hok
  | .performed _ _ _ _, ⟨h, hk⟩ => ⟨EvolvesBy.mono h hok, fun w x => mono hPQ hok (hk w x)⟩
  | .outOfFuel, _ => trivial
  | .stuck, _ => trivial

/-- The evolution of the state an outcome ends in, if it ends in one. -/
theorem fault {s₀ : State} {t : State × World} (h : EvolvesBy ok s₀ t.1) (f : Fault) :
    (Outcome.fault f t : Outcome (State × World) α).Within ok P s₀ := by
  cases f
  · exact h
  · trivial

theorem bind {s₀ : State} {f : α → State × World → Outcome (State × World) β}
    (hf : ∀ a t, P a → EvolvesBy ok s₀ t.1 → (f a t).Within ok Q s₀) :
    ∀ {o : Outcome (State × World) α}, o.Within ok P s₀ → (o.bind f).Within ok Q s₀
  | .done a t, ⟨ha, h⟩ => hf a t ha h
  | .raised _ _, h => h
  | .jumped _ _, h => h
  | .panicked _ _, h => h
  | .performed _ _ _ _, ⟨h, hk⟩ => ⟨h, fun w x => bind hf (hk w x)⟩
  | .outOfFuel, _ => trivial
  | .stuck, _ => trivial

theorem handle {s₀ : State} {g : Value → State × World → Outcome (State × World) α}
    (hg : ∀ e t, EvolvesBy ok s₀ t.1 → (g e t).Within ok P s₀) :
    ∀ {o : Outcome (State × World) α}, o.Within ok P s₀ → (o.handle g).Within ok P s₀
  | .done _ _, h => h
  | .raised e t, h => hg e t h
  | .jumped _ _, h => h
  | .panicked _ _, h => h
  | .performed _ _ _ _, ⟨h, hk⟩ => ⟨h, fun w x => handle hg (hk w x)⟩
  | .outOfFuel, _ => trivial
  | .stuck, _ => trivial

theorem turn {R : Value → Prop} {s₀ : State} :
    ∀ {o : Outcome (State × World) Value}, o.Within ok R s₀ → o.turn.Within ok (fun _ => True) s₀
  | .done _ _, h => ⟨trivial, h.2⟩
  | .raised _ _, h => h
  | .jumped .brk _, h => ⟨trivial, h⟩
  | .jumped .cont _, h => ⟨trivial, h⟩
  | .jumped (.ret _) _, h => h
  | .performed _ _ _ _, ⟨h, hk⟩ => ⟨h, fun w x => turn (hk w x)⟩
  | .panicked _ _, h => h
  | .outOfFuel, _ => trivial
  | .stuck, _ => trivial

theorem unbind_state {s : State} {x : Name} {v : Value} {t : State × World}
    (h : EvolvesBy ok (InPlace.bind s x v) t.1) : EvolvesBy ok s (InPlace.memory.unbind t).1 := by
  have henv : t.1.env.tail = s.env := by rw [h.env_eq]; rfl
  show EvolvesBy ok s ⟨t.1.env.tail, t.1.store⟩
  rw [henv]
  exact h.unbind

/-- Ending a scope's binding forgets the writes to its location. -/
theorem unbind {s : State} {x : Name} {v : Value} :
    ∀ {o : Outcome (State × World) α}, o.Within ok P (InPlace.bind s x v) →
      (o.unbind InPlace.memory).Within ok P s
  | .done _ _, h => ⟨h.1, unbind_state h.2⟩
  | .raised _ _, h => unbind_state h
  | .jumped _ _, h => unbind_state h
  | .panicked _ _, h => unbind_state h
  | .performed _ _ _ _, ⟨h, hk⟩ => ⟨unbind_state h, fun w x => unbind (hk w x)⟩
  | .outOfFuel, _ => trivial
  | .stuck, _ => trivial

/-- A handler's outcome on the frames of a state that evolved from `s₀`. -/
theorem lift {s₀ : State} {s : State × World} (h : EvolvesBy ok s₀ s.1) :
    ∀ o : Outcome (State × World) α, (o.lift InPlace.memory s).Within ok (fun _ => True) s₀
  | .done _ _ => ⟨trivial, h⟩
  | .raised _ _ => h
  | .jumped _ _ => h
  | .panicked _ _ => h
  | .performed _ _ _ k => ⟨h, fun w x => lift h (k w x)⟩
  | .outOfFuel => trivial
  | .stuck => trivial

theorem runBody {s₀ : State} {resume : Value → World → Outcome (State × World) Value}
    (hr : ∀ u x, (resume u x).Within ok (fun _ => True) s₀) :
    ∀ {o : Outcome (State × World) Value}, o.Within ok (fun _ => True) s₀ →
      (o.runBody InPlace.memory resume).Within ok (fun _ => True) s₀
  | .performed op u s k, ⟨h, hk⟩ => by
    unfold Outcome.runBody
    split
    · exact bind (fun _ _ _ hs' => lift hs' _) (hr u _)
    · exact ⟨h, fun w x => runBody hr (hk w x)⟩
  | .done _ _, h | .raised _ _, h | .jumped _ _, h | .panicked _ _, h | .outOfFuel, h
  | .stuck, h => h

/-- A `with` evolves as its block and its clauses do (handlers.with). -/
theorem handleWith {s₀ : State} {effect : Name} {control : Bool} {handler : Value}
    {call : Value → Value → State × World → Outcome (State × World) Value}
    (hcall : ∀ c v t, EvolvesBy ok s₀ t.1 → (call c v t).Within ok (fun _ => True) s₀) :
    ∀ {o : Outcome (State × World) Value}, o.Within ok (fun _ => True) s₀ →
      (o.handleWith InPlace.memory effect control handler call).Within ok (fun _ => True) s₀
  | .performed op v s k, ⟨h, hk⟩ => by
    unfold Outcome.handleWith
    split
    · split
      · trivial
      · split
        · exact runBody (fun u x => handleWith hcall (hk u x)) (hcall _ v s h)
        · exact bind (fun u _ _ _ => handleWith hcall (hk u _)) (hcall _ v s h)
    · exact ⟨h, fun w x => handleWith hcall (hk w x)⟩
  | .done _ _, h | .raised _ _, h | .jumped _ _, h | .panicked _ _, h | .outOfFuel, h
  | .stuck, h => h

theorem after {s₀ : State} {g : State × World → Except Fault (State × World)} {t : State × World}
    {o : State × World → Outcome (State × World) α} (hg : ∀ t', g t = .ok t' → t'.1 = t.1)
    (ht : EvolvesBy ok s₀ t.1) (ho : ∀ t', t'.1 = t.1 → (o t').Within ok P s₀) :
    (Outcome.after g t o).Within ok P s₀ := by
  unfold Outcome.after
  cases h : g t with
  | ok t' => exact ho t' (hg t' h)
  | error e => exact fault ht e

theorem evolve_of_fst {s₀ : State} {t t' : State × World} (ht' : t'.1 = t.1)
    (h : EvolvesBy ok s₀ t.1) : EvolvesBy ok s₀ t'.1 := ht' ▸ h

theorem putBack_fst (held : Bool) (cells : List (Name × Ty × Nat)) (t t' : State × World)
    (h : InPlace.memory.putBack held cells t = .ok t') : t'.1 = t.1 :=
  InPlace.frames.putBack_frame held cells h

/-- Putting the values of a `when`'s names back changes no frame (shared.when). -/
theorem release {s₀ : State} (cells : List (Name × Ty × Nat)) :
    ∀ {o : Outcome (State × World) α}, o.Within ok P s₀ →
      (o.release InPlace.memory cells).Within ok P s₀
  | .done _ t, ⟨ha, h⟩ =>
    after (putBack_fst false cells t) h fun _ ht' => ⟨ha, evolve_of_fst ht' h⟩
  | .raised _ t, h => after (putBack_fst false cells t) h fun _ ht' => evolve_of_fst ht' h
  | .jumped _ t, h => after (putBack_fst false cells t) h fun _ ht' => evolve_of_fst ht' h
  | .panicked _ t, h => after (putBack_fst false cells t) h fun _ ht' => evolve_of_fst ht' h
  | .performed _ _ t _, ⟨h, hk⟩ =>
    after (putBack_fst true cells t) h fun _ ht' =>
      ⟨evolve_of_fst ht' h, fun w x => release cells (hk w x)⟩
  | .outOfFuel, _ => trivial
  | .stuck, _ => trivial

/-- Letting go of cells changes no frame. -/
theorem letGo {s₀ : State} (before : World) :
    ∀ {o : Outcome (State × World) α}, o.Within ok P s₀ →
      (o.letGo InPlace.memory before).Within ok P s₀
  | .done _ _, h => h
  | .raised _ _, h => h
  | .jumped _ _, h => h
  | .panicked _ _, h => h
  | .performed _ _ _ _, ⟨h, hk⟩ => ⟨h, fun w x => letGo before (hk w x)⟩
  | .outOfFuel, _ => trivial
  | .stuck, _ => trivial

end Outcome.Within

end Stilt
