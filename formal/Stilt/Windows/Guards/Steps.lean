import Stilt.Windows.Guards.Outcome

/-!
# Steps that keep guarded regions

`Eval.Guards G R P m`: from every valid in-place state whose store has the regions `G`
guarded by the reads `R` (`Regions`), every outcome of `m` evolves by writes disjoint from
each region of `G`, the rests of its performances included, and its values satisfy `P`.
With no region, it says only that `m` evolves its state by writes below its variables.

Each combinator of `Stilt.Semantics` keeps it. A step after another runs from a state that
evolved, whose regions are still guarded; a new binding's scope may read more and hide the
shapes rooted at its name; a write keeps it when every part below the place it writes avoids
the regions. Calls are in `Stilt.Windows.Guards.Call`.
-/

namespace Stilt

open InPlace

variable {α β : Type}

/-- From every valid state whose regions `G` the reads `R` guard, `m` ends in states that
evolved by writes disjoint from each region, with values that satisfy `P`. -/
def Eval.Guards (G : List Path) (R : List Shape) (P : α → Prop) (m : Eval (State × World) α) :
    Prop :=
  ∀ s : State × World, Valid s.1 → Regions G R s.1 → (m s).Within (Avoids G) P s.1

/-- A new binding's location is in the store. -/
theorem InPlace.valid_bind {s : State} (hv : Valid s) (x : Name) (v : Value) :
    Valid (InPlace.bind s x v) := by
  intro xr hxr
  simp only [InPlace.bind, List.mem_cons, List.length_append, List.length_singleton] at hxr ⊢
  rcases hxr with rfl | hxr
  · simp
  · exact Nat.lt_succ_of_lt (hv xr hxr)

namespace Eval.Guards

variable {G : List Path} {R R' : List Shape} {P : α → Prop} {Q : β → Prop}

/-- What keeps the regions that more reads guard keeps those that fewer reads guard. -/
theorem sub {m : Eval (State × World) α} (h : Eval.Guards G R' P m) (hR : ∀ t ∈ R, t ∈ R') :
    Eval.Guards G R P m := fun s hv hr => h s hv (hr.mono hR)

theorem weaken {m : Eval (State × World) α} {P' : α → Prop} (h : Eval.Guards G R P m)
    (hP : ∀ a, P a → P' a) : Eval.Guards G R P' m := fun s hv hr =>
  Outcome.Within.mono hP (fun _ h => h) (h s hv hr)

theorem pure {a : α} (h : P a) : Eval.Guards G R P (Pure.pure a) :=
  fun s _ _ => ⟨h, .refl _ s.1⟩

theorem fail (f : Fault) : Eval.Guards G R P (Eval.fail f : Eval (State × World) α) :=
  fun s _ _ => Outcome.Within.fault (.refl _ s.1) f

theorem outOfFuel : Eval.Guards G R P (Eval.outOfFuel : Eval (State × World) α) :=
  fun _ _ _ => trivial

theorem throw (e : Value) : Eval.Guards G R P (Eval.throw e : Eval (State × World) α) :=
  fun s _ _ => .refl _ s.1

theorem jump (j : Jump) : Eval.Guards G R P (Eval.jump j : Eval (State × World) α) :=
  fun s _ _ => .refl _ s.1

theorem ofExcept (x : Except Fault α) (h : ∀ a, x = .ok a → P a) :
    Eval.Guards G R P (Eval.ofExcept x) := by
  intro s _ _
  cases x with
  | ok a => exact ⟨h a rfl, .refl _ s.1⟩
  | error f => exact Outcome.Within.fault (.refl _ s.1) f

theorem inspect (f : State × World → Except Fault α) (h : ∀ s a, f s = .ok a → P a) :
    Eval.Guards G R P (Eval.inspect f) := fun s hv hr => ofExcept (f s) (h s) s hv hr

/-- Reading and writing the world changes no frame. -/
theorem world (f : World → Except Fault (Value × World)) :
    Eval.Guards G R (fun _ => True) (Eval.world InPlace.memory f) := by
  rintro ⟨fr, x⟩ _ _
  cases hf : f x with
  | ok p =>
    rw [show Eval.world InPlace.memory f (fr, x) = .done p.1 (fr, p.2) from Eval.world_ok hf]
    exact ⟨trivial, .refl _ fr⟩
  | error e =>
    rw [show Eval.world InPlace.memory f (fr, x) = .fault e (fr, x) from Eval.world_error hf]
    exact Outcome.Within.fault (.refl _ fr) e

theorem bind {m : Eval (State × World) α} {f : α → Eval (State × World) β}
    (hm : Eval.Guards G R P m) (hf : ∀ a, P a → Eval.Guards G R Q (f a)) :
    Eval.Guards G R Q (m >>= f) := fun s hv hr =>
  Outcome.Within.bind (fun a t ha ht => (hf a ha t (ht.valid hv) (hr.evolve ht)).base hv ht)
    (hm s hv hr)

theorem ite (b : Bool) {m₁ m₂ : Eval (State × World) α} (h₁ : Eval.Guards G R P m₁)
    (h₂ : Eval.Guards G R P m₂) : Eval.Guards G R P (if b then m₁ else m₂) := by
  cases b
  · exact h₂
  · exact h₁

theorem handle {m : Eval (State × World) α} {h : Value → Eval (State × World) α}
    (hm : Eval.Guards G R P m) (hh : ∀ e, Eval.Guards G R P (h e)) :
    Eval.Guards G R P (Eval.handle m h) := fun s hv hr =>
  Outcome.Within.handle (fun e t ht => (hh e t (ht.valid hv) (hr.evolve ht)).base hv ht)
    (hm s hv hr)

theorem turn {T : Value → Prop} {m : Eval (State × World) Value} (hm : Eval.Guards G R T m) :
    Eval.Guards G R (fun _ => True) (Eval.turn m) := fun s hv hr =>
  Outcome.Within.turn (hm s hv hr)

theorem forEach {body : Value → Eval (State × World) Bool}
    (hb : ∀ v, Eval.Guards G R (fun _ => True) (body v)) :
    ∀ vs : List Value, Eval.Guards G R (fun _ => True) (Eval.forEach body vs)
  | [] => pure trivial
  | v :: vs => by
    unfold Eval.forEach
    refine bind (hb v) fun b _ => ?_
    cases b
    · exact pure trivial
    · exact forEach hb vs

/-- A binding's scope, whose reads may be more and hide the shapes rooted at its name. -/
theorem withVar (x : Name) (v : Value) {m : Eval (State × World) α} (hm : Eval.Guards G R' P m)
    (hR : ∀ t ∈ hide R x, t ∈ R') : Eval.Guards G R P (Eval.withVar InPlace.memory x v m) :=
  fun s hv hr => Outcome.Within.unbind
    (hm (InPlace.memory.bind s x v) (valid_bind hv x v) (hr.bind_hide hR))

theorem withInit (x : Name) (init : Expr) (v : Value) {m : Eval (State × World) α}
    (hm : Eval.Guards G R' P m) (hR : ∀ t ∈ hide R x, t ∈ R') :
    Eval.Guards G R P (Eval.withInit InPlace.memory x init v m) := by
  have : Eval.withInit InPlace.memory x init v m = Eval.withVar InPlace.memory x v m := by
    funext s
    unfold Eval.withInit Eval.withVar Memory.bindInit
    cases init <;> rfl
  rw [this]
  exact withVar x v hm hR

/-- The scopes of a list of bindings, whose reads hide the shapes rooted at their names. -/
theorem withVars {m : Eval (State × World) α} :
    ∀ (bs : List (Name × Value)) {R : List Shape},
      Eval.Guards G ((bs.map Prod.fst).foldl hide R) P m →
        Eval.Guards G R P (Eval.withVars InPlace.memory bs m)
  | [], _, hm => hm
  | (x, v) :: bs, _, hm => withVar x v (withVars bs hm) fun _ h => h

/-- A write whose every part below avoids the regions. -/
theorem update (x : Name) (p : Path) (w : Value)
    (havoid : ∀ (s : State) r, Regions G R s → s.env.lookup x = some r →
      Avoids G (r.toPath ++ p)) :
    Eval.Guards G R (fun _ => True) (Eval.update fun s => InPlace.memory.write s x p w) := by
  intro s _ hr
  have hw' : InPlace.memory.write s x p w = (·, s.2) <$> InPlace.write s.1 x p w := rfl
  unfold Eval.update
  dsimp only
  rw [hw']
  cases hw : InPlace.write s.1 x p w with
  | error f => exact Outcome.Within.fault (.refl _ s.1) f
  | ok s' =>
    obtain ⟨r, hl, he⟩ := write_evolvesBy hw
    exact ⟨trivial, he.mono fun P hP => hP ▸ havoid s.1 r hr hl⟩

theorem perform (op : Operation) (v : Value) :
    Eval.Guards G R (fun _ => True) (Eval.perform InPlace.memory op v) :=
  fun s _ _ => ⟨.refl _ s.1, fun _ _ => ⟨trivial, .refl _ s.1⟩⟩

theorem letGo {m : Eval (State × World) α} (hm : Eval.Guards G R P m) :
    Eval.Guards G R P (Eval.letGo InPlace.memory m) := fun s hv hr =>
  Outcome.Within.letGo _ (hm s hv hr)

theorem release (cells : List (Name × Ty × Nat)) {m : Eval (State × World) α}
    (hm : Eval.Guards G R P m) : Eval.Guards G R P (Eval.release InPlace.memory cells m) :=
  fun s hv hr => Outcome.Within.release cells (hm s hv hr)

theorem asInt {v : Value} : Eval.Guards G R (fun _ => True) (Eval.asInt v) := by
  cases v <;> first | exact pure trivial | exact fail _

theorem asBool {v : Value} : Eval.Guards G R (fun _ => True) (Eval.asBool v) := by
  cases v <;> first | exact pure trivial | exact fail _

theorem asList {v : Value} : Eval.Guards G R (fun _ => True) (Eval.asList v) := by
  cases v <;> first | exact pure trivial | exact fail _

/-- A `when`, whose block's reads hide the shapes rooted at its names (shared.when). -/
theorem held {block : Eval (State × World) Value} (names : List Name) (handles : List Value)
    (hb : Eval.Guards G (names.foldl hide R) (fun _ => True) block) :
    Eval.Guards G R (fun _ => True) (Eval.held InPlace.memory block names handles) := by
  unfold Eval.held
  refine bind (ofExcept _ fun _ _ => trivial) fun cells _ =>
    bind (bind (world _) fun _ _ => asList) fun vs _ => ?_
  by_cases hlen : names.length = vs.length
  · simp only [hlen, ↓reduceIte]
    refine withVars _ (release _ ?_)
    rwa [List.map_fst_zip (Nat.le_of_eq hlen)]
  · simp only [hlen, ↓reduceIte]
    exact fail _

end Eval.Guards

end Stilt
