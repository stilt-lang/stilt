import Stilt.Alloc.Calls
import Stilt.Selection

/-!
# Matches, loops and `when`s that count no allocation

A `match` runs its arm with the parts its pattern binds, each of which allocates nothing when
called when the value doesn't; a `for` loop runs its body with each element; a `when` takes
values out of its cells and puts them back, and its cells keep values that allocate nothing
when called (shared.when). `Eval.Counts` holds of each.
-/

namespace Stilt

variable {D : Decls} {lim : Limited}

theorem Count.putBack_lift (held : Bool) :
    ∀ (cells : List (Name × Ty × Nat)) (c : Nat) (s : Copy.State),
      Count.memory.putBack held cells (Count.lift c s) =
        Count.lift c <$> Copy.memory.putBack held cells s
  | [], _, _ => rfl
  | (x, h) :: rest, c, s => by
    simp only [Memory.putBack, Count.read_lift, Count.world_lift', Count.setWorld_lift]
    cases Copy.memory.read s x [] with
    | error e => rfl
    | ok v => exact Count.putBack_lift held rest c _

theorem putBack_good (held : Bool) : ∀ (cells : List (Name × Ty × Nat)) {s s' : Copy.State},
    State.AllocFree D lim s → Copy.memory.putBack held cells s = .ok s' → State.AllocFree D lim s'
  | [], _, _, hs, h => by cases h; exact hs
  | (x, h) :: rest, (fr, w), s', hs, hp => by
    simp only [Memory.putBack] at hp
    cases hr : Copy.read fr x [] with
    | error e =>
      have : Copy.memory.read (fr, w) x [] = .error e := hr
      rw [this] at hp; cases hp
    | ok v =>
      have : Copy.memory.read (fr, w) x [] = .ok v := hr
      rw [this] at hp
      exact putBack_good held rest (s := (fr, w.put h v held)) ⟨hs.1, hs.2.put h (hs.1.read hr) held⟩ hp

theorem Outcome.after_lift {α : Type} {P : α → Prop} (held : Bool) (cells : List (Name × Ty × Nat))
    (c : Nat) {s : Copy.State} (hs : State.AllocFree D lim s) {o' : Count.State → Outcome Count.State α}
    {o : Copy.State → Outcome Copy.State α}
    (ho : ∀ s', State.AllocFree D lim s' → o' (Count.lift c s') = (o s').atCount c ∧ (o s').Good D lim P) :
    Outcome.after (Count.memory.putBack held cells) (Count.lift c s) o' =
        (Outcome.after (Copy.memory.putBack held cells) s o).atCount c ∧
      (Outcome.after (Copy.memory.putBack held cells) s o).Good D lim P := by
  unfold Outcome.after
  rw [Count.putBack_lift]
  cases hp : Copy.memory.putBack held cells s with
  | ok s' => exact ho s' (putBack_good held cells hs hp)
  | error e => exact ⟨(Outcome.atCount_fault c e s).symm, Outcome.good_fault e s⟩

namespace Eval.Counts

theorem world {f : World → Except Fault (Value × World)}
    (hf : ∀ w v w', w.All (Value.AllocFree D lim) → f w = .ok (v, w') →
      v.AllocFree D lim ∧ w'.All (Value.AllocFree D lim)) :
    Eval.Counts D lim (Value.AllocFree D lim) (Eval.world Count.memory f) (Eval.world Copy.memory f) := by
  intro c s hs
  refine ⟨Count.world_lift _ c s, ?_⟩
  obtain ⟨fr, w⟩ := s
  cases h : f w with
  | ok p =>
    rw [show Eval.world Copy.memory f (fr, w) = .done p.1 (fr, p.2) from Eval.world_ok h]
    obtain ⟨hv, hw⟩ := hf w p.1 p.2 hs.2 h
    exact ⟨hv, hs.1, hw⟩
  | error e =>
    rw [show Eval.world Copy.memory f (fr, w) = .fault e (fr, w) from Eval.world_error h]
    exact Outcome.good_fault e _

theorem release (cells : List (Name × Ty × Nat)) {m' : Eval Count.State Value}
    {m : Eval Copy.State Value} (hm : Eval.Counts D lim (Value.AllocFree D lim) m' m) :
    Eval.Counts D lim (Value.AllocFree D lim) (Eval.release Count.memory cells m')
      (Eval.release Copy.memory cells m) := by
  intro c s hs
  obtain ⟨he, hg⟩ := hm c s hs
  show (m' (Count.lift c s)).release Count.memory cells = ((m s).release Copy.memory cells).atCount c ∧
    ((m s).release Copy.memory cells).Good D lim (Value.AllocFree D lim)
  rw [he]
  cases hms : m s with
  | done a s₁ =>
    rw [hms] at hg
    exact Outcome.after_lift false cells c hg.2 fun s' hs' => ⟨rfl, hg.1, hs'⟩
  | raised e s₁ =>
    rw [hms] at hg
    exact Outcome.after_lift false cells c hg.2 fun s' hs' => ⟨rfl, hg.1, hs'⟩
  | jumped j s₁ =>
    rw [hms] at hg
    exact Outcome.after_lift false cells c hg.2 fun s' hs' => ⟨rfl, hg.1, hs'⟩
  | panicked k s₁ =>
    simp only [Outcome.atCount, Outcome.release, Outcome.after, Count.putBack_lift]
    cases Copy.memory.putBack false cells s₁ with
    | ok s' => exact ⟨rfl, trivial⟩
    | error e => exact ⟨(Outcome.atCount_fault c e _).symm, Outcome.good_fault e _⟩
  | performed _ _ _ _ => rw [hms] at hg; exact hg.elim
  | outOfFuel => exact ⟨rfl, trivial⟩
  | stuck => exact ⟨rfl, trivial⟩

/-- A `when` whose block counts no allocation. -/
theorem held {block' : Eval Count.State Value} {block : Eval Copy.State Value}
    (hb : Eval.Counts D lim (Value.AllocFree D lim) block' block) (names : List Name)
    (handles : List Value) :
    Eval.Counts D lim (Value.AllocFree D lim) (Eval.held Count.memory block' names handles)
      (Eval.held Copy.memory block names handles) := by
  unfold Eval.held
  refine bind (ofExcept (P := fun _ => True) fun _ _ => trivial) fun cells _ => ?_
  refine bind (bind (world fun w v w' hw h => ?_) fun v hv => asList hv) fun vs hvs => ?_
  · cases ht : World.take cells w with
    | error e => rw [ht] at h; cases h
    | ok p =>
      rw [ht] at h
      cases h
      obtain ⟨hvs, hw'⟩ := World.All.take hw ht
      exact ⟨.list hvs, hw'⟩
  · split
    · exact withVars (release _ hb) _ fun xv hm => hvs _ (List.of_mem_zip hm).2
    · exact fail _

theorem armsAllocFree_mem : ∀ {arms : List Arm} {arm : Arm}, armsAllocFree D lim arms = true →
    arm ∈ arms → arm.body.allocFreeIn D lim = true ∧ guardAllocFree D lim arm.guard = true
  | ⟨_, _, _, _⟩ :: arms, arm, hs, hm => by
    simp only [armsAllocFree, Bool.and_eq_true] at hs
    rcases List.mem_cons.1 hm with rfl | hm
    · exact ⟨hs.1.2, hs.1.1⟩
    · exact armsAllocFree_mem hs.2 hm

section Runs

variable {run' : Expr → Eval Count.State Value} {run : Expr → Eval Copy.State Value}
  (h : CountsRun D lim run' run)
include h

theorem select {arms : List Arm} (harms : armsAllocFree D lim arms = true) {v : Value}
    (hv : v.AllocFree D lim) :
    Eval.Counts D lim (Value.AllocFree D lim) (Eval.select Count.memory run' arms v)
      (Eval.select Copy.memory run arms v) := by
  refine Eval.select_rel (fun m m' => Eval.Counts D lim (Value.AllocFree D lim) m' m) (fail _)
    (fun arm ha _ us hm _ => ?_) fun arm ha g hg us hu _ m m' hmm => ?_
  · exact withVars (h _ (armsAllocFree_mem harms ha).1) _ fun xv hxv =>
      arm.pattern.matchOn_parts Value.AllocFree.passesToParts hv hm xv.2 (List.of_mem_zip hxv).2
  · obtain ⟨hb, hgd⟩ := armsAllocFree_mem harms ha
    rw [hg] at hgd
    simp only [guardAllocFree] at hgd
    obtain ⟨q, -, hq⟩ := Pattern.mem_ways hu
    have hparts : ∀ xv ∈ arm.binders.zip us, xv.2.AllocFree D lim := fun xv hxv =>
      q.matchOn_parts Value.AllocFree.passesToParts hv hq xv.2 (List.of_mem_zip hxv).2
    unfold Eval.tryWay
    exact bind (withVars (bind (h g hgd) fun b _ => asBool b) _ hparts) fun b _ =>
      ite b (withVars (h _ hb) _ hparts) hmm

theorem loop (x : Name) {e body : Expr} (he : e.allocFreeIn D lim = true)
    (hb : body.allocFreeIn D lim = true) :
    Eval.Counts D lim (Value.AllocFree D lim) (Eval.loop Count.memory run' x e body)
      (Eval.loop Copy.memory run x e body) := by
  unfold Eval.loop
  exact bind (bind (h e he) fun v hv => asList hv) fun vs hvs =>
    bind (forEach (fun v hv => withVar hv (turn (h body hb))) vs hvs) fun _ _ => pure .unit

end Runs

end Eval.Counts

end Stilt
