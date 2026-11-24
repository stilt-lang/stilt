import Stilt.Related
import Stilt.Moves.Observed
import Stilt.InPlace.Leave

/-!
# Copy-in, copy-out sees through marks

Copy-in, copy-out reads a mark as the variable: `eval` has one case for both,
`Memory.bindInit` binds a copy, and `Copy.enter` binds a `moved` argument as a
value (values.passing-values and values.inout-argument-order). So a step of
the evaluator run on a frame, its marks erased, ends as it ends on the frame,
erased (`Eval.Erases`): the two outcomes are related by `Outcome.erasing`,
which relates a value, a raise, a jump, a panic and a performance to their
erasures, and the rests of two performances once resumed with a value and its
erasure. So the two runs show the same, erased (`Outcome.Rel.observe_erase`).
This module proves it of the combinators the evaluator is written with, calls
included; `Stilt.Moves.Oracle` proves it of every expression.
-/

namespace Stilt

variable {α β : Type}

/-- A cell with the marks of its value erased. -/
def Cell.erase (c : Cell) : Cell := { c with value := c.value.erase }

/-- A world with the marks of its cells' values erased: what it has written and has yet to
read are as they were. -/
def World.erase (w : World) : World := { w with cells := w.cells.map Cell.erase }

/-- A state of copy-in, copy-out with the marks of its frame and of its world erased. -/
def eraseState (s : Copy.State) : Copy.State := (eraseBindings s.1, s.2.erase)

/-- What a run and the run of its erasure relate: a value and its erasure by
`f`, a raise, a jump, a panic and a performance and their erasures, each with a
state and its erasure (values.passing-values); and a performance resumed with a
value and its erasure, in a world and its erasure. -/
def Outcome.erasing (f : α → α) : Outcome.Relation Copy.State Copy.State α α where
  done a s b t := b = f a ∧ t = eraseState s
  raised e s e' t := e' = e.erase ∧ t = eraseState s
  jumped j s j' t := j' = j.erase ∧ t = eraseState s
  panicked k s k' t := k' = k ∧ t = eraseState s
  performed op v s op' v' t := op' = op ∧ v' = v.erase ∧ t = eraseState s
  resume _ w x w' x' := w' = w.erase ∧ x' = x.erase

/-- A body's outcome and its erasure's, ended as `main`'s: what the second
shows is what the first shows, erased. -/
theorem Outcome.Rel.observe_erase {o o' : Outcome Copy.State Value}
    (h : o.Rel (Outcome.erasing Value.erase) o') : o.leaveBody.observe.erase = o'.leaveBody.observe := by
  cases o <;> cases o' <;> first | exact absurd h id | rfl | skip
  all_goals first
    | (obtain ⟨rfl, rfl⟩ := h; rfl)
    | (rename_i j _ j' _; obtain ⟨rfl, rfl⟩ := h; cases j <;> rfl)

/-- A body's outcome and its erasure's, ended as `main`'s, write the same output. -/
theorem Outcome.Rel.output_erase {o o' : Outcome Copy.State Value}
    (h : o.Rel (Outcome.erasing Value.erase) o') : o.leaveBody.output = o'.leaveBody.output := by
  cases o <;> cases o' <;> first | exact absurd h id | rfl | skip
  all_goals first
    | (obtain ⟨-, rfl⟩ := h; rfl)
    | (rename_i j _ j' _; obtain ⟨rfl, rfl⟩ := h; cases j <;> rfl)

/-- `erasing` relates the same raises, jumps and panics, whatever erases the
values. -/
theorem Outcome.erasing_escapes {f : α → α} {g : β → β} :
    (Outcome.erasing f).Escapes (Outcome.erasing g) :=
  ⟨fun _ _ _ _ h => h, fun _ _ _ _ h => h, fun _ _ _ _ h => h, fun _ _ _ _ _ _ h => h,
    fun _ _ _ _ _ h => h⟩

/-- `m'` runs as `m` with the marks erased: from the erasure of any frame, it
ends as `m` ends from that state, erased, with `f` erasing the result (values.passing-values). -/
def Eval.Erases (f : α → α) (m m' : Eval Copy.State α) : Prop :=
  ∀ s, (m s).Rel (Outcome.erasing f) (m' (eraseState s))

theorem eraseBindings_tail :
    ∀ l : List (Name × Value), (eraseBindings l).tail = eraseBindings l.tail
  | [] | _ :: _ => rfl

/-- In copy-in, copy-out, every initializer binds a copy, a last use's
included (values.passing-values). -/
theorem Copy.withInit_eq (x : Name) (init : Expr) (v : Value) (m : Eval Copy.State α) :
    Eval.withInit Copy.memory x init v m = Eval.withVar Copy.memory x v m := by
  funext s
  unfold Eval.withInit Eval.withVar
  cases init <;> rfl

namespace Eval.Erases

variable {f : α → α} {g : β → β}

theorem pure (f : α → α) (a : α) : Erases f (Eval.pure a) (Eval.pure (f a)) := fun _ => ⟨rfl, rfl⟩

theorem fail (f : α → α) (flt : Fault) : Erases f (Eval.fail flt) (Eval.fail flt) := by
  intro s
  cases flt
  · exact ⟨rfl, rfl⟩
  · trivial

theorem throw (f : α → α) (v : Value) : Erases f (Eval.throw v) (Eval.throw v.erase) :=
  fun _ => ⟨rfl, rfl⟩

theorem jump (f : α → α) (j : Jump) : Erases f (Eval.jump j) (Eval.jump j.erase) :=
  fun _ => ⟨rfl, rfl⟩

/-- A turn of a loop's body ends alike, its marks erased. -/
theorem turn {m m' : Eval Copy.State Value} (hm : Erases Value.erase m m') :
    Erases id (Eval.turn m) (Eval.turn m') := by
  intro s
  refine Outcome.Rel.turn (hm s) (fun _ _ _ _ h => ⟨rfl, h.2⟩) (fun _ _ _ _ h => h) ?_
    (fun _ _ _ _ h => h) Outcome.erasing_escapes.performs
  rintro j s j' t ⟨rfl, rfl⟩
  cases j <;> exact ⟨rfl, rfl⟩

theorem bind {m m' : Eval Copy.State α} {k k' : α → Eval Copy.State β} (hm : Erases f m m')
    (hk : ∀ a, Erases g (k a) (k' (f a))) : Erases g (m >>= k) (m' >>= k') := by
  intro s
  show ((m s).bind fun a s' => k a s').Rel _ ((m' (eraseState s)).bind fun a s' => k' a s')
  refine Outcome.Rel.bind (hm s) Outcome.erasing_escapes ?_
  rintro a s₁ b t ⟨rfl, rfl⟩
  exact hk a s₁

theorem ofExcept (f : α → α) (x : Except Fault α) :
    Erases f (Eval.ofExcept x) (Eval.ofExcept (x.map f)) := by
  intro s
  cases x with
  | ok _ => exact ⟨rfl, rfl⟩
  | error flt => exact fail f flt s

/-- Reading and writing the world, as `f'` does on the world erased what `f` does, its value
and the world it leaves erased. -/
theorem world {f f' : World → Except Fault (Value × World)}
    (h : ∀ x, f' x.erase = (f x).map fun p => (p.1.erase, p.2.erase)) :
    Erases Value.erase (Eval.world Copy.memory f) (Eval.world Copy.memory f') := by
  rintro ⟨fr, x⟩
  cases hf : f x with
  | ok p =>
    have hf' : f' x.erase = .ok (p.1.erase, p.2.erase) := by rw [h, hf]; rfl
    rw [show Eval.world Copy.memory f (fr, x) = .done p.1 (fr, p.2) from Eval.world_ok hf,
      show Eval.world Copy.memory f' (eraseState (fr, x)) =
          .done p.1.erase (eraseBindings fr, p.2.erase) from Eval.world_ok hf']
    exact ⟨rfl, rfl⟩
  | error e =>
    have hf' : f' x.erase = .error e := by rw [h, hf]; rfl
    rw [show Eval.world Copy.memory f (fr, x) = .fault e (fr, x) from Eval.world_error hf,
      show Eval.world Copy.memory f' (eraseState (fr, x)) = .fault e (eraseBindings fr, x.erase)
        from Eval.world_error hf']
    exact fail Value.erase e (fr, x)

theorem inspect {r r' : Copy.State → Except Fault α}
    (h : ∀ s, r' (eraseState s) = (r s).map f) :
    Erases f (Eval.inspect r) (Eval.inspect r') := by
  intro s
  show (Eval.ofExcept (r s) s).Rel _ (Eval.ofExcept (r' (eraseState s)) (eraseState s))
  rw [h]
  exact ofExcept f (r s) s

theorem update {u u' : Copy.State → Except Fault Copy.State}
    (h : ∀ s, u' (eraseState s) = (u s).map eraseState) :
    Erases id (Eval.update u) (Eval.update u') := by
  intro s
  unfold Eval.update
  rw [h]
  cases u s with
  | ok _ => exact ⟨rfl, rfl⟩
  | error flt => exact fail id flt s

theorem ite (b : Bool) {m₁ m₁' m₂ m₂' : Eval Copy.State α} (h₁ : Erases f m₁ m₁')
    (h₂ : Erases f m₂ m₂') :
    Erases f (if b then m₁ else m₂) (if b then m₁' else m₂') := by
  cases b
  · exact h₂
  · exact h₁

theorem withVar {m m' : Eval Copy.State α} (x : Name) (v : Value) (hm : Erases f m m') :
    Erases f (Eval.withVar Copy.memory x v m) (Eval.withVar Copy.memory x v.erase m') := by
  intro s
  have hb : Copy.memory.bind (eraseState s) x v.erase =
      eraseState (Copy.memory.bind s x v) := rfl
  have ht : ∀ s t : Copy.State, t = eraseState s →
      Copy.memory.unbind t = eraseState (Copy.memory.unbind s) := by
    rintro s t rfl
    show ((eraseBindings s.1).tail, s.2.erase) = (eraseBindings s.1.tail, s.2.erase)
    rw [eraseBindings_tail]
  show ((m _).unbind Copy.memory).Rel _
    ((m' (Copy.memory.bind (eraseState s) x v.erase)).unbind _)
  rw [hb]
  exact Outcome.Rel.unbind Copy.memory Copy.memory (hm _)
    (fun _ _ _ _ h => ⟨h.1, ht _ _ h.2⟩) (fun _ _ _ _ h => ⟨h.1, ht _ _ h.2⟩)
    (fun _ _ _ _ h => ⟨h.1, ht _ _ h.2⟩) (fun _ _ _ _ h => ⟨h.1, ht _ _ h.2⟩)
    (fun _ _ _ _ _ _ h => ⟨h.1, h.2.1, ht _ _ h.2.2⟩) fun _ _ _ _ _ h => h

theorem withInit {m m' : Eval Copy.State α} (x : Name) (init init' : Expr) (v : Value)
    (hm : Erases f m m') :
    Erases f (Eval.withInit Copy.memory x init v m)
      (Eval.withInit Copy.memory x init' v.erase m') := by
  rw [Copy.withInit_eq, Copy.withInit_eq]
  exact withVar x v hm

theorem withVars {m m' : Eval Copy.State α} (hm : Erases f m m') :
    ∀ bs, Erases f (Eval.withVars Copy.memory bs m)
      (Eval.withVars Copy.memory (eraseBindings bs) m')
  | [] => hm
  | (x, v) :: bs => withVar x v (withVars hm bs)

theorem handle {m m' : Eval Copy.State α} {h h' : Value → Eval Copy.State α}
    (hm : Erases f m m') (hh : ∀ e, Erases f (h e) (h' e.erase)) :
    Erases f (Eval.handle m h) (Eval.handle m' h') := by
  intro s
  show ((m s).handle fun e s' => h e s').Rel _ ((m' (eraseState s)).handle fun e s' => h' e s')
  refine Outcome.Rel.handle (hm s) (fun _ _ _ _ hc => hc) (fun _ _ _ _ hc => hc)
    (fun _ _ _ _ hc => hc) Outcome.erasing_escapes.performs ?_
  rintro e s₁ e' t ⟨rfl, rfl⟩
  exact hh e s₁

theorem forEach {body body' : Value → Eval Copy.State Bool}
    (h : ∀ v, Erases id (body v) (body' v.erase)) :
    ∀ vs, Erases id (Eval.forEach body vs) (Eval.forEach body' (eraseValues vs))
  | [] => pure id ()
  | v :: vs => bind (h v) fun g => ite g (forEach h vs) (pure id ())

end Eval.Erases

/-! ## Calls -/

/-- The parameters of a call bound to their arguments, with the arguments'
marks erased (values.passing-values). -/
def eraseBound (bound : List (Name × Passed)) : List (Name × Passed) :=
  bound.map fun ya => (ya.1, ya.2.erase)

/-- A last use passed to a `let` parameter is passed as a value. -/
theorem bindArgs_erase : ∀ (ps : List Param) (args : List Passed),
    bindArgs ps (args.map Passed.erase) = (bindArgs ps args).map eraseBound
  | [], [] | [], _ :: _ | _ :: _, [] => rfl
  | p :: ps, a :: args => by
    cases hm : p.mode <;> cases a <;> simp [bindArgs, Passed.erase, hm, bindArgs_erase ps args] <;>
      cases bindArgs ps args <;> rfl

open InPlace (copyEnterStep copyLeaveStep copy_enter_eq copy_leave_eq) in
/-- The start of a call copies each argument in, erased if the caller's frame
is (values.inout-argument-order). -/
theorem Copy.enter_erase (caller : Copy.Frame) :
    ∀ (bound : List (Name × Passed)) (fr : Copy.Frame),
      Copy.frames.enter (eraseBindings caller) (eraseBindings fr) (eraseBound bound) =
        (Copy.frames.enter caller fr bound).map eraseBindings
  | [], _ => rfl
  | (y, a) :: bound, fr => by
    rw [copy_enter_eq, copy_enter_eq] at *
    simp only [eraseBound, List.map_cons, List.foldlM_cons]
    have ih := Copy.enter_erase caller bound
    simp only [copy_enter_eq, eraseBound] at ih
    cases a with
    | value v | moved _ v => exact ih ((y, v) :: fr)
    | place x p =>
      simp only [Passed.erase, copyEnterStep, Copy.read_erase]
      cases Copy.read caller x p with
      | error _ => rfl
      | ok v => exact ih ((y, v) :: fr)

open InPlace (copyEnterStep copyLeaveStep copy_enter_eq copy_leave_eq) in
/-- The end of a call writes each `inout` argument back, erased if the frames
are (values.inout-arguments and values.inout-argument-order). -/
theorem Copy.leave_erase (callee : Copy.Frame) :
    ∀ (bound : List (Name × Passed)) (fr : Copy.Frame),
      Copy.frames.leave (eraseBindings fr) (eraseBindings callee) (eraseBound bound) =
        (Copy.frames.leave fr callee bound).map eraseBindings
  | [], _ => rfl
  | (y, a) :: bound, fr => by
    rw [copy_leave_eq, copy_leave_eq] at *
    simp only [eraseBound, List.map_cons, List.foldlM_cons]
    have ih := Copy.leave_erase callee bound
    simp only [copy_leave_eq, eraseBound] at ih
    cases a with
    | value v | moved _ v => exact ih fr
    | place x p =>
      simp only [Passed.erase, copyLeaveStep, Copy.read_erase]
      cases Copy.read callee y [] with
      | error _ => rfl
      | ok v =>
        simp only [Except.map, Except.bind, Copy.write_erase]
        cases Copy.write fr x p v with
        | error _ => rfl
        | ok fr' => exact ih fr'

/-- The start of a call, from an erased state, is the start of the call
erased, in the world erased. -/
theorem Copy.memory_enter_erase (s : Copy.State) (captured : Copy.Frame)
    (bound : List (Name × Passed)) :
    Copy.memory.enter (eraseState s) (eraseBindings captured) (eraseBound bound) =
      (Copy.memory.enter s captured bound).map eraseState := by
  show (·, s.2.erase) <$> Copy.frames.enter (eraseBindings s.1) (eraseBindings captured)
    (eraseBound bound) = _
  rw [Copy.enter_erase]
  show _ = ((·, s.2) <$> Copy.frames.enter s.1 captured bound).map eraseState
  cases Copy.frames.enter s.1 captured bound <;> rfl

/-- Writing an erased value to an erased state is writing the value, erased. -/
theorem Copy.memory_write_erase (s : Copy.State) (x : Name) (p : Path) (v : Value) :
    Copy.memory.write (eraseState s) x p v.erase = (Copy.memory.write s x p v).map eraseState := by
  show (·, s.2.erase) <$> Copy.write (eraseBindings s.1) x p v.erase = _
  rw [Copy.write_erase]
  show _ = ((·, s.2) <$> Copy.write s.1 x p v).map eraseState
  cases Copy.write s.1 x p v <;> rfl

/-- The end of a call, from erased states, is the end of the call erased, in
the callee's world. -/
theorem Copy.memory_leave_erase (s s' : Copy.State) (bound : List (Name × Passed)) :
    Copy.memory.leave (eraseState s) (eraseState s') (eraseBound bound) =
      (Copy.memory.leave s s' bound).map eraseState := by
  show (·, s'.2.erase) <$> Copy.frames.leave (eraseBindings s.1) (eraseBindings s'.1)
    (eraseBound bound) = _
  rw [Copy.leave_erase]
  show _ = ((·, s'.2) <$> Copy.frames.leave s.1 s'.1 bound).map eraseState
  cases Copy.frames.leave s.1 s'.1 bound <;> rfl

theorem erasing_fault {α : Type} {f : α → α} (flt : Fault) (s : Copy.State) :
    (Outcome.fault flt s : Outcome Copy.State α).Rel (Outcome.erasing f)
      (Outcome.fault flt (eraseState s)) :=
  Outcome.Rel.fault (R := Outcome.erasing f) (fun _ => ⟨rfl, rfl⟩) flt

/-- A callee's outcome and its erasure's leave the call alike, the caller's
frame and the arguments erased: a value, a raise, a `return`, a panic and a
performance write the same `inout` arguments back, erased (values.inout-arguments),
and a performance's rest leaves it alike when it ends. -/
theorem Outcome.Rel.leaveCall_erase (bound : List (Name × Passed)) (s : Copy.State)
    {o o' : Outcome Copy.State Value} (h : o.Rel (Outcome.erasing Value.erase) o') :
    (o.leaveCall Copy.memory bound s).Rel (Outcome.erasing Value.erase)
      (o'.leaveCall Copy.memory (eraseBound bound) (eraseState s)) := by
  have hl : ∀ s', Copy.memory.leave (eraseState s) (eraseState s') (eraseBound bound) =
      (Copy.memory.leave s s' bound).map eraseState := fun s' => Copy.memory_leave_erase s s' bound
  induction o generalizing o' with
  | performed op v s' k ih =>
    cases o' with
    | performed op' v' t k' =>
      obtain ⟨⟨rfl, rfl, rfl⟩, hk⟩ := h
      simp only [Outcome.leaveCall, hl]
      cases Copy.memory.leave s s' bound with
      | error flt => exact erasing_fault flt _
      | ok _ => exact ⟨⟨rfl, rfl, rfl⟩, fun w x w' x' hw => ih w x (hk w x w' x' hw)⟩
    | _ => exact absurd h id
  | jumped j s' =>
    cases o' <;> try exact absurd h id
    obtain ⟨rfl, rfl⟩ := h
    cases j with
    | ret v =>
      simp only [Outcome.leaveCall, Jump.erase, hl]
      cases Copy.memory.leave s s' bound with
      | error flt => exact erasing_fault flt _
      | ok _ => exact ⟨rfl, rfl⟩
    | brk | cont => trivial
  | outOfFuel => cases o' <;> first | exact absurd h id | trivial
  | stuck => cases o' <;> first | exact absurd h id | trivial
  | _ =>
    cases o' <;> try exact absurd h id
    obtain ⟨rfl, rfl⟩ := h
    simp only [Outcome.leaveCall, hl]
    cases Copy.memory.leave s _ bound with
    | error flt => exact erasing_fault flt _
    | ok _ => exact ⟨rfl, rfl⟩

/-- A call runs alike on erased states, with its arguments and its closure's
captured variables erased (values.passing-values, values.inout-arguments and values.inout-argument-order). -/
theorem Eval.Erases.invoke {body body' : Eval Copy.State Value} (captured : List (Name × Value))
    (params : List Param) (args : List Passed) (h : Erases Value.erase body body') :
    Erases Value.erase (Eval.invoke Copy.memory captured params args body)
      (Eval.invoke Copy.memory (eraseBindings captured) params (args.map Passed.erase) body') := by
  intro s
  unfold Eval.invoke
  rw [bindArgs_erase]
  cases bindArgs params args with
  | none => trivial
  | some bound =>
    simp only [Option.map_some, Copy.memory_enter_erase]
    cases Copy.memory.enter s captured bound with
    | error flt => exact erasing_fault flt s
    | ok callee => exact (h callee).leaveCall_erase bound s

end Stilt
