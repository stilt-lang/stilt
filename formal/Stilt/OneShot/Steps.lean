import Stilt.OneShot.Handling
import Stilt.InPlace.Steps

/-!
# Steps that resume at most so often

Each combinator of `Stilt.Semantics` keeps `Eval.OneShot` in copy-in, copy-out,
whatever its order of write-back: a sequence of steps adds their counts, and a
step that makes or moves values makes one-shot ones from one-shot ones.
-/

namespace Stilt

namespace Eval.OneShot

variable {α β : Type} {P : α → Prop} {Q : β → Prop} {n : Nat}

theorem mono {m : Eval Copy.State α} {k : Nat} (h : Eval.OneShot n P m) (hnk : n ≤ k)
    {Q : α → Prop} (hPQ : ∀ a, P a → Q a) : Eval.OneShot k Q m := fun s hs =>
  (h s hs).mono hPQ hnk

theorem pure {a : α} (h : P a) : Eval.OneShot n P (Pure.pure a) := fun _ hs => ⟨h, hs⟩

theorem bind {a b : Nat} {m : Eval Copy.State α} {f : α → Eval Copy.State β}
    (hm : Eval.OneShot a P m) (hf : ∀ x, P x → Eval.OneShot b Q (f x)) :
    Eval.OneShot (a + b) Q (m >>= f) := fun s hs =>
  Outcome.OneShot.bind (fun x s' hx hs' => hf x hx s' hs') (hm s hs)

/-- `bind` at a count that bounds the sum. -/
theorem bindLe {a b : Nat} {m : Eval Copy.State α} {f : α → Eval Copy.State β}
    (hm : Eval.OneShot a P m) (hf : ∀ x, P x → Eval.OneShot b Q (f x)) (h : a + b ≤ n) :
    Eval.OneShot n Q (m >>= f) :=
  (bind hm hf).mono h fun _ h => h

theorem stuck : Eval.OneShot n P (Eval.fail .stuck : Eval Copy.State α) := fun _ _ => trivial

theorem fail {f : Fault} : Eval.OneShot n P (Eval.fail f : Eval Copy.State α) := fun _ hs =>
  Outcome.OneShot.fault hs

theorem outOfFuel : Eval.OneShot n P (Eval.outOfFuel : Eval Copy.State α) := fun _ _ => trivial

theorem ofExcept {x : Except Fault α} (h : ∀ a, x = .ok a → P a) :
    Eval.OneShot n P (Eval.ofExcept x) := by
  intro s hs
  cases x with
  | ok a => exact ⟨h a rfl, hs⟩
  | error f => exact Outcome.OneShot.fault hs

/-- Reading and writing the world, which gives values of `R`. -/
theorem world (w : WriteBack) {R : Value → Prop} (f : World → Except Fault (Value × World))
    (h : ∀ x v x', x.All Value.OneShot → f x = .ok (v, x') → R v ∧ x'.All Value.OneShot) :
    Eval.OneShot n R (Eval.world (Copy.memoryWith w) f) := by
  rintro ⟨fr, x⟩ hs
  cases hf : f x with
  | ok p =>
    rw [show Eval.world (Copy.memoryWith w) f (fr, x) = .done p.1 (fr, p.2) from Eval.world_ok hf]
    obtain ⟨hv, hx⟩ := h x p.1 p.2 hs.2 hf
    exact ⟨hv, hs.1, hx⟩
  | error e =>
    rw [show Eval.world (Copy.memoryWith w) f (fr, x) = .fault e (fr, x) from Eval.world_error hf]
    exact Outcome.OneShot.fault hs

theorem inspect {f : Copy.State → Except Fault α} (h : ∀ s a, State.OneShot s → f s = .ok a → P a) :
    Eval.OneShot n P (Eval.inspect f) := fun s hs => ofExcept (h s · hs) s hs

theorem update {f : Copy.State → Except Fault Copy.State}
    (h : ∀ s s', State.OneShot s → f s = .ok s' → State.OneShot s') :
    Eval.OneShot n (fun _ => True) (Eval.update f) := by
  intro s hs
  unfold Eval.update
  cases hf : f s with
  | ok s' => exact ⟨trivial, h s s' hs hf⟩
  | error e => exact Outcome.OneShot.fault hs

theorem throw {e : Value} (he : e.OneShot) : Eval.OneShot n P (Eval.throw e : Eval Copy.State α) :=
  fun _ hs => ⟨he, hs⟩

theorem jump {j : Jump} (hj : j.OneShot) : Eval.OneShot n P (Eval.jump j : Eval Copy.State α) :=
  fun _ hs => ⟨hj, hs⟩

theorem handle {a b : Nat} {m : Eval Copy.State α} {h : Value → Eval Copy.State α}
    (hm : Eval.OneShot a P m) (hh : ∀ e, e.OneShot → Eval.OneShot b P (h e)) :
    Eval.OneShot (a + b) P (Eval.handle m h) := fun s hs =>
  Outcome.OneShot.handle (fun e s' he hs' => hh e he s' hs') (hm s hs)

theorem turn {R : Value → Prop} {m : Eval Copy.State Value} (hm : Eval.OneShot n R m) :
    Eval.OneShot n (fun _ => True) (Eval.turn m) := fun s hs => (hm s hs).turn

theorem ite (b : Bool) {m₁ m₂ : Eval Copy.State α} (h₁ : Eval.OneShot n P m₁)
    (h₂ : Eval.OneShot n P m₂) : Eval.OneShot n P (if b then m₁ else m₂) := by
  cases b
  · exact h₂
  · exact h₁

theorem asBool {v : Value} : Eval.OneShot n (fun _ => True) (Eval.asBool v : Eval Copy.State Bool) := by
  cases v <;> first | exact pure trivial | exact stuck

theorem asInt {v : Value} : Eval.OneShot n (fun _ => True) (Eval.asInt v : Eval Copy.State Int) := by
  cases v <;> first | exact pure trivial | exact stuck

theorem asList {v : Value} (hv : v.OneShot) :
    Eval.OneShot n (fun vs : List Value => ∀ u ∈ vs, u.OneShot) (Eval.asList v) := by
  cases v <;> first | exact stuck | skip
  cases hv with
  | list h => exact pure h

/-- Performing an operation on a one-shot value: one `resume` more when it is
`resume`. -/
theorem perform (w : WriteBack) {op : Operation} {v : Value} (hv : v.OneShot) :
    Eval.OneShot (if op = Operation.resume then 1 else 0) Value.OneShot
      (Eval.perform (Copy.memoryWith w) op v : Eval Copy.State Value) := fun _ hs =>
  Outcome.OneShot.performed hv hs (fun hop => by simp [hop]) fun _ _ hw hx => ⟨hw, hs.1, hx⟩

theorem forEach {body : Value → Eval Copy.State Bool}
    (hb : ∀ v, v.OneShot → Eval.OneShot 0 (fun _ => True) (body v)) :
    ∀ vs : List Value, (∀ v ∈ vs, v.OneShot) → Eval.OneShot 0 (fun _ => True) (Eval.forEach body vs)
  | [], _ => pure trivial
  | v :: vs, h => by
    unfold Eval.forEach
    refine bindLe (b := 0) (hb v (h v List.mem_cons_self)) (fun b _ => ?_) (Nat.le_refl 0)
    cases b
    · exact pure trivial
    · exact forEach hb vs fun u hu => h u (List.mem_cons_of_mem _ hu)

section

variable (w : WriteBack)

theorem withVar {x : Name} {v : Value} {m : Eval Copy.State α} (hv : v.OneShot)
    (hm : Eval.OneShot n P m) : Eval.OneShot n P (Eval.withVar (Copy.memoryWith w) x v m) :=
  fun s hs => (hm ((x, v) :: s.1, s.2) ⟨hs.1.cons (x := x) hv, hs.2⟩).unbind w

theorem withInit {x : Name} {init : Expr} {v : Value} {m : Eval Copy.State α} (hv : v.OneShot)
    (hm : Eval.OneShot n P m) :
    Eval.OneShot n P (Eval.withInit (Copy.memoryWith w) x init v m) := by
  have : Eval.withInit (Copy.memoryWith w) x init v m = Eval.withVar (Copy.memoryWith w) x v m := by
    funext s
    unfold Eval.withInit Eval.withVar Memory.bindInit
    cases init <;> rfl
  rw [this]
  exact withVar w hv hm

theorem withVars {m : Eval Copy.State α} (hm : Eval.OneShot n P m) :
    ∀ (bs : List (Name × Value)), (∀ xv ∈ bs, xv.2.OneShot) →
      Eval.OneShot n P (Eval.withVars (Copy.memoryWith w) bs m)
  | [], _ => hm
  | (x, v) :: bs, h =>
    withVar w (h (x, v) List.mem_cons_self) (withVars hm bs fun xv hx => h xv (List.mem_cons_of_mem _ hx))

theorem read (x : Name) :
    Eval.OneShot n Value.OneShot (Eval.inspect fun s => (Copy.memoryWith w).read s x []) :=
  inspect fun _ _ hs h => Frame.OneShot.read hs.1 h

theorem capture (keep : Name → Bool) :
    Eval.OneShot n (fun c : List (Name × Value) => ∀ xv ∈ c, xv.2.OneShot)
      (Eval.inspect ((Copy.memoryWith w).capture · keep)) :=
  inspect fun _ _ hs h => by cases h; exact fun xv hxv => hs.1 xv (mem_of_mem_newestOf hxv)

end

theorem declare (D : Decls) (R : Name) {written : List (Name × Value)}
    (hw : ∀ fv ∈ written, fv.2.OneShot) :
    Eval.OneShot n Value.OneShot (Eval.declare D R written) := by
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

end Eval.OneShot

end Stilt
