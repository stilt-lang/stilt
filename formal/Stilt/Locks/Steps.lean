import Stilt.Locks.Handling
import Stilt.InPlace.Steps

/-!
# Steps that take no cell

Each combinator of `Stilt.Semantics` but a `when`'s keeps `Eval.TakesNone` in copy-in,
copy-out, whatever its order of write-back: a sequence of steps that take no cell takes
none, an operation on the world writes, reads or makes a cell but holds none, and a step
that makes or moves values makes lock-free ones from lock-free ones (shared.locks).
-/

namespace Stilt

variable {D : Decls} {L : List Name}

namespace Eval.TakesNone

variable {α β : Type} {P : α → Prop} {Q : β → Prop}

theorem mono {m : Eval Copy.State α} (h : Eval.TakesNone D L P m) {R : α → Prop}
    (hPR : ∀ a, P a → R a) : Eval.TakesNone D L R m := fun s hs => (h s hs).mono hPR

theorem pure {a : α} (h : P a) : Eval.TakesNone D L P (Pure.pure a) := fun s hs =>
  ⟨h, hs, .refl s.2⟩

theorem bind {m : Eval Copy.State α} {f : α → Eval Copy.State β}
    (hm : Eval.TakesNone D L P m) (hf : ∀ x, P x → Eval.TakesNone D L Q (f x)) :
    Eval.TakesNone D L Q (m >>= f) := fun s hs =>
  Outcome.TakesNone.bind (fun x s' hx hs' => hf x hx s' hs') (hm s hs)

theorem stuck : Eval.TakesNone D L P (Eval.fail .stuck : Eval Copy.State α) := fun _ _ => trivial

theorem fail {f : Fault} : Eval.TakesNone D L P (Eval.fail f : Eval Copy.State α) := fun s _ =>
  Outcome.TakesNone.fault (.refl s.2)

theorem outOfFuel : Eval.TakesNone D L P (Eval.outOfFuel : Eval Copy.State α) := fun _ _ => trivial

theorem ofExcept {x : Except Fault α} (h : ∀ a, x = .ok a → P a) :
    Eval.TakesNone D L P (Eval.ofExcept x) := by
  intro s hs
  cases x with
  | ok a => exact ⟨h a rfl, hs, .refl s.2⟩
  | error f => exact Outcome.TakesNone.fault (.refl s.2)

/-- An operation on the world, which holds no cell. -/
theorem run (w : WriteBack) {o : Op} {vs : List Value} (hvs : ∀ v ∈ vs, v.LockFree D L) :
    Eval.TakesNone D L (Value.LockFree D L) (Eval.world (Copy.memoryWith w) (o.run vs)) := by
  rintro ⟨fr, x⟩ hs
  cases hf : o.run vs x with
  | ok p =>
    rw [show Eval.world (Copy.memoryWith w) (o.run vs) (fr, x) = .done p.1 (fr, p.2) from
      Eval.world_ok hf]
    exact ⟨Op.run_hereditary Value.LockFree.hereditary .unit hvs hf, hs,
      (World.HoldsNoMore.refl x).run hf⟩
  | error e =>
    rw [show Eval.world (Copy.memoryWith w) (o.run vs) (fr, x) = .fault e (fr, x) from
      Eval.world_error hf]
    exact Outcome.TakesNone.fault (.refl x)

theorem inspect {f : Copy.State → Except Fault α}
    (h : ∀ s a, Frame.LockFree D L s.1 → f s = .ok a → P a) :
    Eval.TakesNone D L P (Eval.inspect f) := fun s hs => ofExcept (h s · hs) s hs

theorem update {f : Copy.State → Except Fault Copy.State}
    (h : ∀ s s', Frame.LockFree D L s.1 → f s = .ok s' → Frame.LockFree D L s'.1 ∧ s'.2 = s.2) :
    Eval.TakesNone D L (fun _ => True) (Eval.update f) := by
  intro s hs
  unfold Eval.update
  cases hf : f s with
  | ok s' =>
    obtain ⟨h₁, h₂⟩ := h s s' hs hf
    exact ⟨trivial, h₁, h₂ ▸ .refl s.2⟩
  | error e => exact Outcome.TakesNone.fault (.refl s.2)

theorem throw {e : Value} (he : e.LockFree D L) :
    Eval.TakesNone D L P (Eval.throw e : Eval Copy.State α) := fun s hs => ⟨he, hs, .refl s.2⟩

theorem jump {j : Jump} (hj : j.LockFree D L) :
    Eval.TakesNone D L P (Eval.jump j : Eval Copy.State α) := fun s hs => ⟨hj, hs, .refl s.2⟩

theorem handle {m : Eval Copy.State α} {h : Value → Eval Copy.State α}
    (hm : Eval.TakesNone D L P m) (hh : ∀ e, e.LockFree D L → Eval.TakesNone D L P (h e)) :
    Eval.TakesNone D L P (Eval.handle m h) := fun s hs =>
  Outcome.TakesNone.handle (fun e s' he hs' => hh e he s' hs') (hm s hs)

theorem turn {R : Value → Prop} {m : Eval Copy.State Value} (hm : Eval.TakesNone D L R m) :
    Eval.TakesNone D L (fun _ => True) (Eval.turn m) := fun s hs => (hm s hs).turn

theorem ite (b : Bool) {m₁ m₂ : Eval Copy.State α} (h₁ : Eval.TakesNone D L P m₁)
    (h₂ : Eval.TakesNone D L P m₂) : Eval.TakesNone D L P (if b then m₁ else m₂) := by
  cases b
  · exact h₂
  · exact h₁

theorem asBool {v : Value} :
    Eval.TakesNone D L (fun _ => True) (Eval.asBool v : Eval Copy.State Bool) := by
  cases v <;> first | exact pure trivial | exact stuck

theorem asInt {v : Value} :
    Eval.TakesNone D L (fun _ => True) (Eval.asInt v : Eval Copy.State Int) := by
  cases v <;> first | exact pure trivial | exact stuck

theorem asList {v : Value} (hv : v.LockFree D L) :
    Eval.TakesNone D L (fun vs : List Value => ∀ u ∈ vs, u.LockFree D L) (Eval.asList v) := by
  cases v <;> first | exact stuck | skip
  cases hv with
  | list h => exact pure h

/-- Performing an operation on a lock-free value, whose rest goes on from the frame the
performance left, in the world it is resumed in. -/
theorem perform (w : WriteBack) {op : Operation} {v : Value} (hv : v.LockFree D L) :
    Eval.TakesNone D L (Value.LockFree D L)
      (Eval.perform (Copy.memoryWith w) op v : Eval Copy.State Value) := fun s hs =>
  ⟨hv, hs, .refl s.2, fun _ y hu => ⟨hu, hs, .refl y⟩⟩

theorem forEach {body : Value → Eval Copy.State Bool}
    (hb : ∀ v, v.LockFree D L → Eval.TakesNone D L (fun _ => True) (body v)) :
    ∀ vs : List Value, (∀ v ∈ vs, v.LockFree D L) →
      Eval.TakesNone D L (fun _ => True) (Eval.forEach body vs)
  | [], _ => pure trivial
  | v :: vs, h => by
    unfold Eval.forEach
    refine bind (hb v (h v List.mem_cons_self)) (fun b _ => ?_)
    cases b
    · exact pure trivial
    · exact forEach hb vs fun u hu => h u (List.mem_cons_of_mem _ hu)

section

variable (w : WriteBack)

theorem withVar {x : Name} {v : Value} {m : Eval Copy.State α} (hv : v.LockFree D L)
    (hm : Eval.TakesNone D L P m) :
    Eval.TakesNone D L P (Eval.withVar (Copy.memoryWith w) x v m) :=
  fun s hs => (hm ((x, v) :: s.1, s.2) (hs.cons (x := x) hv)).unbind w

theorem withInit {x : Name} {init : Expr} {v : Value} {m : Eval Copy.State α}
    (hv : v.LockFree D L) (hm : Eval.TakesNone D L P m) :
    Eval.TakesNone D L P (Eval.withInit (Copy.memoryWith w) x init v m) := by
  have : Eval.withInit (Copy.memoryWith w) x init v m =
      Eval.withVar (Copy.memoryWith w) x v m := by
    funext s
    unfold Eval.withInit Eval.withVar Memory.bindInit
    cases init <;> rfl
  rw [this]
  exact withVar w hv hm

theorem withVars {m : Eval Copy.State α} (hm : Eval.TakesNone D L P m) :
    ∀ (bs : List (Name × Value)), (∀ xv ∈ bs, xv.2.LockFree D L) →
      Eval.TakesNone D L P (Eval.withVars (Copy.memoryWith w) bs m)
  | [], _ => hm
  | (x, v) :: bs, h =>
    withVar w (h (x, v) List.mem_cons_self)
      (withVars hm bs fun xv hx => h xv (List.mem_cons_of_mem _ hx))

theorem read (x : Name) :
    Eval.TakesNone D L (Value.LockFree D L)
      (Eval.inspect fun s => (Copy.memoryWith w).read s x []) :=
  inspect fun _ _ hs h => Frame.LockFree.read hs h

theorem capture :
    Eval.TakesNone D L (fun c : List (Name × Value) => ∀ xv ∈ c, xv.2.LockFree D L)
      (Eval.inspect (Copy.memoryWith w).capture) :=
  inspect fun _ _ hs h => by cases h; exact hs

/-- `with h { block }` lets go of the cells its dropped rests hold. -/
theorem letGo {m : Eval Copy.State α} (hm : Eval.TakesNone D L P m) :
    Eval.TakesNone D L P (Eval.letGo (Copy.memoryWith w) m) := fun s hs =>
  (hm s hs).letGo w _

end

theorem declare (D' : Decls) (R : Name) {written : List (Name × Value)}
    (hw : ∀ fv ∈ written, fv.2.LockFree D L) :
    Eval.TakesNone D L (Value.LockFree D L) (Eval.declare D' R written) := by
  unfold Eval.declare
  split
  · split
    · rename_i fields hfields
      refine pure (.record fun fv hfv => ?_)
      obtain ⟨⟨f, τ⟩, _, ha⟩ := InPlace.Sim.mapM_mem hfields fv hfv
      simp only [Option.map_eq_some_iff] at ha
      obtain ⟨v, hv, rfl⟩ := ha
      exact hw _ (mem_of_lookup hv)
    · exact stuck
  · exact stuck

end Eval.TakesNone

end Stilt
