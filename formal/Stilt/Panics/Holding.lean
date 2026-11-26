import Stilt.Panics.Steps

/-!
# A `when` without panics

A `when` adds no panic of its own but `deadlock`, which `without panic` doesn't rule out
(shared.when-on-value-already-held): holding its cells panics with that kind when one is
held, and otherwise takes out of the world panic-free values, which its block's panic-free
code works on; putting each name's value back in its cell, however the block ends, keeps
every cell's value panic-free (shared.when).
-/

namespace Stilt

variable {lim : Limited}

/-- The cells that handles name: no panic, only stuck at a value that is no handle. -/
theorem Value.cellOf_calm : ∀ handles : List Value,
    CalmTo (fun _ => True) (handles.mapM Value.cellOf)
  | [] => CalmTo.ok trivial
  | v :: vs => by
    rw [List.mapM_cons]
    refine CalmTo.bind (P := fun _ => True) ?_ fun _ _ =>
      CalmTo.bind (Value.cellOf_calm vs) fun _ _ => CalmTo.ok trivial
    cases v <;> first | exact CalmTo.ok trivial | exact CalmTo.stuck

/-- Holding cells panics only with `deadlock` (shared.when-on-value-already-held). -/
theorem World.take_error {hs : List (Ty × Nat)} {w : World} {e : Fault}
    (h : World.take hs w = .error e) : e = .panic .deadlock := by
  unfold World.take at h
  split at h
  · split at h
    · cases h
    · cases h; rfl
  · cases h; rfl

/-- Putting back the values of a panic-free state's names keeps it panic-free. -/
theorem putBack_calm (w : WriteBack) (held : Bool) : ∀ (cells : List (Name × Ty × Nat))
    {s : Copy.State}, State.PanicFree lim s →
      CalmTo (State.PanicFree lim) ((Copy.memoryWith w).putBack held cells s)
  | [], _, hs => CalmTo.ok hs
  | (x, h) :: rest, (fr, wd), hs => by
    simp only [Memory.putBack]
    exact CalmTo.bind (Frame.PanicFree.read hs.1 x (p := []) (fun _ h => nomatch h)) fun v hv =>
      putBack_calm w held rest ⟨hs.1, hs.2.put h hv held⟩

namespace Outcome.PanicFree

variable {α : Type} {P : α → Prop} (w : WriteBack)

theorem after {held : Bool} {cells : List (Name × Ty × Nat)} {s : Copy.State}
    {o : Copy.State → Outcome Copy.State α} (hs : State.PanicFree lim s)
    (ho : ∀ s', State.PanicFree lim s' → (o s').PanicFree lim P) :
    (Outcome.after ((Copy.memoryWith w).putBack held cells) s o).PanicFree lim P := by
  have hc := putBack_calm w held cells hs
  unfold Outcome.after
  split
  · rename_i s' h
    exact ho s' (hc.2 s' h)
  · rename_i e h
    rw [h] at hc
    exact Eval.PanicFree.fault hc.1 hs

/-- A `when` puts back panic-free values however its block ends. -/
theorem release (cells : List (Name × Ty × Nat)) :
    ∀ {o : Outcome Copy.State α}, o.PanicFree lim P → (o.release (Copy.memoryWith w) cells).PanicFree lim P
  | .done _ _, h | .raised _ _, h | .jumped _ _, h | .panicked _ _, h =>
    after w h.2 fun _ hs' => ⟨h.1, hs'⟩
  | .performed _ _ _ _, ⟨hv, hs, hk⟩ =>
    after w hs fun _ hs' => ⟨hv, hs', fun u x hu hx => release cells (hk u x hu hx)⟩
  | .outOfFuel, h | .stuck, h => h

end Outcome.PanicFree

namespace Eval.PanicFree

variable {G : List Known} (w : WriteBack)

/-- A `when` whose block keeps to panic-free code, with no fact about its names, panics
only as its block does, or with `deadlock` (shared.when-on-value-already-held). -/
theorem held {block : Eval Copy.State Value} (names : List Name) (handles : List Value)
    (hb : Eval.PanicFree lim (withoutNames G names) (Value.PanicFree lim) block) :
    Eval.PanicFree lim G (Value.PanicFree lim) (Eval.held (Copy.memoryWith w) block names handles) := by
  intro s hs hz
  have hc := Value.cellOf_calm handles
  show (Outcome.PanicFree lim) _ (((Eval.ofExcept (handles.mapM Value.cellOf)) >>= fun cells =>
    (Eval.world (Copy.memoryWith w) (fun x => (World.take cells x).map fun p => (Value.list p.1, p.2))
      >>= Eval.asList) >>= fun vs =>
    if names.length = vs.length then
      Eval.withVars (Copy.memoryWith w) (names.zip vs)
        (Eval.release (Copy.memoryWith w) (names.zip cells) block)
    else Eval.fail .stuck) s)
  cases hm : handles.mapM Value.cellOf with
  | error e =>
    rw [hm] at hc
    cases e with
    | panic k => exact ⟨.inl (hc.1 k rfl), hs⟩
    | stuck => trivial
  | ok cells =>
    obtain ⟨fr, x⟩ := s
    show (Outcome.PanicFree lim) _ (((Eval.world (Copy.memoryWith w) _ (fr, x)).bind _).bind _)
    cases ht : World.take cells x with
    | error e =>
      rw [show Eval.world (Copy.memoryWith w) (fun x => (World.take cells x).map
          fun p => (Value.list p.1, p.2)) (fr, x) = .fault e (fr, x) from
        Eval.world_error (by rw [ht]; rfl), World.take_error ht]
      exact ⟨.inr rfl, hs⟩
    | ok p =>
      obtain ⟨vs, x'⟩ := p
      rw [show Eval.world (Copy.memoryWith w) (fun x => (World.take cells x).map
          fun p => (Value.list p.1, p.2)) (fr, x) = .done (.list vs) (fr, x') from
        Eval.world_ok (by rw [ht]; rfl)]
      obtain ⟨hvs, hx'⟩ := World.All.take hs.2 ht
      show (Outcome.PanicFree lim) _ ((if names.length = vs.length then
        Eval.withVars (Copy.memoryWith w) (names.zip vs)
          (Eval.release (Copy.memoryWith w) (names.zip cells) block)
        else Eval.fail .stuck) (fr, x'))
      split
      · rename_i hlen
        refine withVars w (names.zip vs) (fun xv hm => hvs _ (List.of_mem_zip hm).2) ?_ (fr, x')
          ⟨hs.1, hx'⟩ hz
        rw [List.map_fst_zip (by omega)]
        exact fun s' hs' hz' => Outcome.PanicFree.release w _ (hb s' hs' hz')
      · exact stuck _ ⟨hs.1, hx'⟩ hz

end Eval.PanicFree

end Stilt
