import Stilt.Panics.Writes
import Stilt.Semantics
import Stilt.InPlace.Enter

/-!
# Runs keep what they don't write

Evaluating `e` in copy-in, copy-out, whatever its order of write-back, ends with
a frame that has the variables it started with, each with its value unless
`e.writes` names it (`eval_keeps`). An assignment writes its root, and a call
writes back only the places its `inout` arguments name; the callee runs in a
frame of its own, and every binding ends with its scope.
-/

namespace Stilt

/-- How an evaluation from the frame `s` that keeps the variables outside `W`, and
the lengths of the lists outside `L`, may end: with a value that `P` holds of, a
raise or a jump, each from a frame that keeps them, or a performance from such a
frame whose rest, resumed with any value in any world, again ends so. -/
def Outcome.Keeps {α : Type} (W L : List Name) (P : α → Prop) (s : Copy.Frame) :
    Outcome Copy.State α → Prop
  | .done a s' => P a ∧ Frame.Keeps W L s s'.1
  | .raised _ s' => Frame.Keeps W L s s'.1
  | .jumped _ s' => Frame.Keeps W L s s'.1
  | .performed _ _ s' k => Frame.Keeps W L s s'.1 ∧ ∀ w x, Outcome.Keeps W L P s (k w x)
  | .panicked _ _ => True
  | .outOfFuel => True
  | .stuck => True

/-- From every state, `m` keeps the variables outside `W`, and the lengths of the
lists outside `L`, of its frame. -/
def Eval.Keeps {α : Type} (W L : List Name) (P : α → Prop) (m : Eval Copy.State α) : Prop :=
  ∀ s, Outcome.Keeps W L P s.1 (m s)

theorem Except.ok_bind' {ε α β : Type} (a : α) (f : α → Except ε β) : (Except.ok a >>= f) = f a := rfl

theorem Except.error_bind' {ε α β : Type} (e : ε) (f : α → Except ε β) :
    (Except.error e >>= f) = .error e := rfl

namespace Outcome.Keeps

variable {α β : Type} {W L : List Name} {P : α → Prop} {Q : β → Prop}

/-- What an outcome keeps from a later frame, it keeps from an earlier one. -/
theorem base {s₀ s : Copy.Frame} (h : Frame.Keeps W L s₀ s) :
    ∀ {o : Outcome Copy.State α}, o.Keeps W L P s → o.Keeps W L P s₀
  | .done _ _, ⟨ha, h'⟩ => ⟨ha, h.trans h'⟩
  | .raised _ _, h' => h.trans h'
  | .jumped _ _, h' => h.trans h'
  | .performed _ _ _ _, ⟨h', hk⟩ => ⟨h.trans h', fun w x => base h (hk w x)⟩
  | .panicked _ _, _ => trivial
  | .outOfFuel, _ => trivial
  | .stuck, _ => trivial

theorem bind {s₀ : Copy.Frame} {f : α → Copy.State → Outcome Copy.State β}
    (hf : ∀ a s, P a → Frame.Keeps W L s₀ s.1 → (f a s).Keeps W L Q s₀) :
    ∀ {o : Outcome Copy.State α}, o.Keeps W L P s₀ → (o.bind f).Keeps W L Q s₀
  | .done a s, ⟨ha, h⟩ => hf a s ha h
  | .raised _ _, h => h
  | .jumped _ _, h => h
  | .performed _ _ _ _, ⟨h, hk⟩ => ⟨h, fun w x => bind hf (hk w x)⟩
  | .panicked _ _, _ => trivial
  | .outOfFuel, _ => trivial
  | .stuck, _ => trivial

theorem handle {s₀ : Copy.Frame} {h : Value → Copy.State → Outcome Copy.State α}
    (hh : ∀ e s, Frame.Keeps W L s₀ s.1 → (h e s).Keeps W L P s₀) :
    ∀ {o : Outcome Copy.State α}, o.Keeps W L P s₀ → (o.handle h).Keeps W L P s₀
  | .done _ _, h' => h'
  | .raised e s, h' => hh e s h'
  | .jumped _ _, h' => h'
  | .performed _ _ _ _, ⟨h', hk⟩ => ⟨h', fun w x => handle hh (hk w x)⟩
  | .panicked _ _, _ => trivial
  | .outOfFuel, _ => trivial
  | .stuck, _ => trivial

theorem turn {R : Value → Prop} {s₀ : Copy.Frame} :
    ∀ {o : Outcome Copy.State Value}, o.Keeps W L R s₀ → o.turn.Keeps W L (fun _ => True) s₀
  | .done _ _, h => ⟨trivial, h.2⟩
  | .raised _ _, h => h
  | .jumped .brk _, h => ⟨trivial, h⟩
  | .jumped .cont _, h => ⟨trivial, h⟩
  | .jumped (.ret _) _, h => h
  | .performed _ _ _ _, ⟨h, hk⟩ => ⟨h, fun w x => turn (hk w x)⟩
  | .panicked _ _, _ => trivial
  | .outOfFuel, _ => trivial
  | .stuck, _ => trivial

theorem unbind (w : WriteBack) {s : Copy.State} {x : Name} {v : Value} :
    ∀ {o : Outcome Copy.State α}, o.Keeps W L P ((Copy.memoryWith w).bind s x v).1 →
      (o.unbind (Copy.memoryWith w)).Keeps W L P s.1
  | .done _ _, h => ⟨h.1, Frame.Keeps.tail h.2⟩
  | .raised _ _, h => Frame.Keeps.tail h
  | .jumped _ _, h => Frame.Keeps.tail h
  | .performed _ _ _ _, ⟨h, hk⟩ => ⟨Frame.Keeps.tail h, fun w' x' => unbind w (hk w' x')⟩
  | .panicked _ _, _ => trivial
  | .outOfFuel, _ => trivial
  | .stuck, _ => trivial

/-- A handler's outcome lifted to a state whose frame keeps from `s₀` keeps from it. -/
theorem lift (w : WriteBack) {s₀ : Copy.Frame} {s : Copy.State} (h : Frame.Keeps W L s₀ s.1) :
    ∀ o : Outcome Copy.State α, (o.lift (Copy.memoryWith w) s).Keeps W L (fun _ => True) s₀
  | .done _ _ => ⟨trivial, h⟩
  | .raised _ _ => h
  | .jumped _ _ => h
  | .panicked _ _ => trivial
  | .performed _ _ _ k => ⟨h, fun w' x => lift w h (k w' x)⟩
  | .outOfFuel => trivial
  | .stuck => trivial

theorem runBody (w : WriteBack) {s₀ : Copy.Frame} {resume : Value → World → Outcome Copy.State Value}
    (hr : ∀ u x, (resume u x).Keeps W L (fun _ => True) s₀) :
    ∀ {o : Outcome Copy.State Value}, o.Keeps W L (fun _ => True) s₀ →
      (o.runBody (Copy.memoryWith w) resume).Keeps W L (fun _ => True) s₀
  | .performed op u s k, ⟨h, hk⟩ => by
    unfold Outcome.runBody
    split
    · exact bind (fun _ _ _ hs' => lift w hs' _) (hr u _)
    · exact ⟨h, fun w' x => runBody w hr (hk w' x)⟩
  | .done _ _, h | .raised _ _, h | .jumped _ _, h | .panicked _ _, h | .outOfFuel, h
  | .stuck, h => h

/-- A `with` keeps what its block and its clauses keep (handlers.with). -/
theorem handleWith (w : WriteBack) {s₀ : Copy.Frame} {effect : Name} {control : Bool}
    {handler : Value} {call : Value → Value → Copy.State → Outcome Copy.State Value}
    (hcall : ∀ c v s, Frame.Keeps W L s₀ s.1 → (call c v s).Keeps W L (fun _ => True) s₀) :
    ∀ {o : Outcome Copy.State Value}, o.Keeps W L (fun _ => True) s₀ →
      (o.handleWith (Copy.memoryWith w) effect control handler call).Keeps W L (fun _ => True) s₀
  | .performed op v s k, ⟨h, hk⟩ => by
    unfold Outcome.handleWith
    split
    · split
      · trivial
      · split
        · exact runBody w (fun u x => handleWith w hcall (hk u x)) (hcall _ v s h)
        · exact bind (fun u _ _ _ => handleWith w hcall (hk u _)) (hcall _ v s h)
    · exact ⟨h, fun w' x => handleWith w hcall (hk w' x)⟩
  | .done _ _, h | .raised _ _, h | .jumped _ _, h | .panicked _ _, h | .outOfFuel, h
  | .stuck, h => h

end Outcome.Keeps

namespace Eval.Keeps

variable {α β : Type} {W L : List Name} {P : α → Prop} {Q : β → Prop}

theorem fault (f : Fault) (s : Copy.State) (s₀ : Copy.Frame) :
    Outcome.Keeps W L P s₀ (Outcome.fault f s : Outcome Copy.State α) := by
  cases f <;> trivial

theorem pure {a : α} (h : P a) : Eval.Keeps W L P (Pure.pure a) := fun s => ⟨h, .refl s.1⟩

theorem bind {m : Eval Copy.State α} {f : α → Eval Copy.State β} (hm : Eval.Keeps W L P m)
    (hf : ∀ a, P a → Eval.Keeps W L Q (f a)) : Eval.Keeps W L Q (m >>= f) := fun s =>
  Outcome.Keeps.bind (fun a s' ha hs' => (hf a ha s').base hs') (hm s)

theorem fail (f : Fault) : Eval.Keeps W L P (Eval.fail f : Eval Copy.State α) := fun s => fault f s s.1

theorem ofExcept (x : Except Fault α) (h : ∀ a, x = .ok a → P a) :
    Eval.Keeps W L P (Eval.ofExcept x) := by
  intro s
  cases x with
  | ok a => exact ⟨h a rfl, .refl s.1⟩
  | error f => exact fault f s s.1

/-- Reading and writing the world keeps every frame. -/
theorem world (w : WriteBack) (f : World → Except Fault (Value × World)) :
    Eval.Keeps W L (fun _ => True) (Eval.world (Copy.memoryWith w) f) := by
  rintro ⟨fr, x⟩
  cases hf : f x with
  | ok p =>
    rw [show Eval.world (Copy.memoryWith w) f (fr, x) = .done p.1 (fr, p.2) from Eval.world_ok hf]
    exact ⟨trivial, .refl fr⟩
  | error e =>
    rw [show Eval.world (Copy.memoryWith w) f (fr, x) = .fault e (fr, x) from Eval.world_error hf]
    exact fault _ _ fr

theorem inspect (f : Copy.State → Except Fault α) (h : ∀ s a, f s = .ok a → P a) :
    Eval.Keeps W L P (Eval.inspect f) := fun s => ofExcept (f s) (h s) s

theorem throw (e : Value) : Eval.Keeps W L P (Eval.throw e : Eval Copy.State α) := fun s => .refl s.1

theorem jump (j : Jump) : Eval.Keeps W L P (Eval.jump j : Eval Copy.State α) := fun s => .refl s.1

theorem handle {m : Eval Copy.State α} {h : Value → Eval Copy.State α} (hm : Eval.Keeps W L P m)
    (hh : ∀ e, Eval.Keeps W L P (h e)) : Eval.Keeps W L P (Eval.handle m h) := fun s =>
  Outcome.Keeps.handle (fun e s' hs' => (hh e s').base hs') (hm s)

theorem turn {R : Value → Prop} {m : Eval Copy.State Value} (hm : Eval.Keeps W L R m) :
    Eval.Keeps W L (fun _ => True) (Eval.turn m) := fun s => Outcome.Keeps.turn (hm s)

theorem forEach {body : Value → Eval Copy.State Bool}
    (hb : ∀ v, Eval.Keeps W L (fun _ => True) (body v)) :
    ∀ vs : List Value, Eval.Keeps W L (fun _ => True) (Eval.forEach body vs)
  | [] => pure trivial
  | v :: vs => by
    unfold Eval.forEach
    refine bind (hb v) fun b _ => ?_
    cases b
    · exact pure trivial
    · exact forEach hb vs

theorem ite (b : Bool) {m₁ m₂ : Eval Copy.State α} (h₁ : Eval.Keeps W L P m₁)
    (h₂ : Eval.Keeps W L P m₂) : Eval.Keeps W L P (if b then m₁ else m₂) := by
  cases b
  · exact h₂
  · exact h₁

section

variable (w : WriteBack)

theorem withVar (x : Name) (v : Value) {m : Eval Copy.State α} (hm : Eval.Keeps W L P m) :
    Eval.Keeps W L P (Eval.withVar (Copy.memoryWith w) x v m) := fun s =>
  Outcome.Keeps.unbind w (hm ((Copy.memoryWith w).bind s x v))

theorem withInit (x : Name) (init : Expr) (v : Value) {m : Eval Copy.State α}
    (hm : Eval.Keeps W L P m) : Eval.Keeps W L P (Eval.withInit (Copy.memoryWith w) x init v m) := by
  have : Eval.withInit (Copy.memoryWith w) x init v m = Eval.withVar (Copy.memoryWith w) x v m := by
    funext s
    unfold Eval.withInit Eval.withVar Memory.bindInit
    cases init <;> rfl
  rw [this]
  exact withVar w x v hm

theorem withVars {m : Eval Copy.State α} (hm : Eval.Keeps W L P m) :
    ∀ bs : List (Name × Value), Eval.Keeps W L P (Eval.withVars (Copy.memoryWith w) bs m)
  | [] => hm
  | (x, v) :: bs => withVar w x v (withVars hm bs)

/-- The places a call passes `inout` are rooted in `W`, and in `L` when the place is a
whole variable. -/
def _root_.Stilt.Passed.RootIn (W L : List Name) : Passed → Prop
  | .place x path => x ∈ W ∧ (path = [] → x ∈ L)
  | _ => True

theorem leave {callee : Copy.Frame} :
    ∀ {fr fr' : Copy.Frame} (params : List (Name × Passed)), (∀ ya ∈ params, ya.2.RootIn W L) →
      Copy.leave fr callee params = .ok fr' → Frame.Keeps W L fr fr'
  | fr, fr', [], _, h => by cases h; exact .refl fr
  | fr, fr', (y, a) :: params, hps, h => by
    have hrest : ∀ ya ∈ params, ya.2.RootIn W L := fun ya h => hps ya (List.mem_cons_of_mem _ h)
    unfold Copy.leave at h
    rw [List.foldlM_cons] at h
    cases a with
    | value v | moved _ v => exact leave params hrest h
    | place x path =>
      have hx := hps (y, .place x path) List.mem_cons_self
      simp only at h
      cases hr : Copy.read callee y [] with
      | error e => rw [hr, Except.error_bind', Except.error_bind'] at h; cases h
      | ok v =>
        rw [hr, Except.ok_bind'] at h
        cases hw : Copy.write fr x path v with
        | error e => rw [hw, Except.error_bind'] at h; cases h
        | ok fr'' =>
          rw [hw, Except.ok_bind'] at h
          exact (Frame.Keeps.write hx.1 hx.2 hw).trans (leave params hrest h)

theorem memoryWith_leave (s s' : Copy.State) (bound : List (Name × Passed)) :
    (Copy.memoryWith w).leave s s' bound = (·, s'.2) <$> Copy.leave s.1 s'.1 (w.order bound) := rfl

theorem memoryWith_enter (s : Copy.State) (captured : List (Name × Value))
    (bound : List (Name × Passed)) :
    (Copy.memoryWith w).enter s captured bound = (·, s.2) <$> Copy.enter s.1 captured bound := rfl

/-- Leaving a call, from the caller's state `s`, changes its frame only where the
call writes back, however the callee ended, and so does each rest of a
performance that leaves it. -/
theorem leaveCall {bound : List (Name × Passed)} {s : Copy.State}
    (hl : ∀ s' fr, Copy.leave s.1 s' (w.order bound) = .ok fr → Frame.Keeps W L s.1 fr) :
    ∀ o : Outcome Copy.State Value,
      (o.leaveCall (Copy.memoryWith w) bound s).Keeps W L (fun _ => True) s.1
  | .done v s' | .jumped (.ret v) s' => by
    simp only [Outcome.leaveCall, memoryWith_leave]
    cases h : Copy.leave s.1 s'.1 (w.order bound) with
    | ok fr => exact ⟨trivial, hl s'.1 fr h⟩
    | error f => exact fault f _ _
  | .raised e s' => by
    simp only [Outcome.leaveCall, memoryWith_leave]
    cases h : Copy.leave s.1 s'.1 (w.order bound) with
    | ok fr => exact hl s'.1 fr h
    | error f => exact fault f _ _
  | .jumped .brk _ | .jumped .cont _ => trivial
  | .panicked k s' => by
    simp only [Outcome.leaveCall, memoryWith_leave]
    cases Copy.leave s.1 s'.1 (w.order bound) with
    | ok _ => trivial
    | error f => exact fault f _ _
  | .performed op v s' k => by
    simp only [Outcome.leaveCall, memoryWith_leave]
    cases h : Copy.leave s.1 s'.1 (w.order bound) with
    | ok fr => exact ⟨hl s'.1 fr h, fun w' x => leaveCall hl (k w' x)⟩
    | error f => exact fault f _ _
  | .outOfFuel => trivial
  | .stuck => trivial

/-- A call changes the caller's frame only where it writes back its `inout` arguments. -/
theorem invoke (captured : List (Name × Value)) (params : List Param) {passed : List Passed}
    (hp : ∀ q ∈ passed, q.RootIn W L) (body : Eval Copy.State Value) :
    Eval.Keeps W L (fun _ => True) (Eval.invoke (Copy.memoryWith w) captured params passed body) := by
  intro s
  unfold Eval.invoke
  cases hbind : bindArgs params passed with
  | none => trivial
  | some bound =>
    have hsnd := (InPlace.bindArgs_spec hbind).2
    have hb : ∀ ya ∈ w.order bound, ya.2.RootIn W L := fun ya hya =>
      hp _ (hsnd ▸ List.mem_map_of_mem ((w.perm bound).mem_iff.1 hya))
    dsimp only
    rw [memoryWith_enter]
    cases Copy.enter s.1 captured bound with
    | error f => exact fault f s s.1
    | ok callee =>
      exact leaveCall w (fun _ _ h => leave (w.order bound) hb h) (body (callee, s.2))

theorem call (D : Decls) (run : Expr → Eval Copy.State Value) (f : Value) {passed : List Passed}
    (hp : ∀ q ∈ passed, q.RootIn W L) :
    Eval.Keeps W L (fun _ => True) (Eval.call D (Copy.memoryWith w) run f passed) := by
  cases f with
  | closure captured params result ρ body => exact invoke w captured params hp _
  | function name types rows =>
    unfold Eval.call
    dsimp only
    cases D.fn? name with
    | none => exact fail _
    | some d => exact invoke w [] d.params hp _
  | _ => exact fail _

theorem callAs (D : Decls) (run : Expr → Eval Copy.State Value) (control : Bool) (f : Value)
    {passed : List Passed} (hp : ∀ q ∈ passed, q.RootIn W L) :
    Eval.Keeps W L (fun _ => True) (Eval.callAs D (Copy.memoryWith w) run control f passed) := by
  unfold Eval.callAs
  split
  · exact fail _
  · exact call w D run f hp

end

end Eval.Keeps

end Stilt
