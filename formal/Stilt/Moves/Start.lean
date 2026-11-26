import Stilt.Moves.Hand

/-!
# The start of a call

Both models start a call from the live bindings of the caller alone: the
places it reads are of live variables, and each last use passes the value its
variable holds. So the callee's frame and state are those that copy-in,
copy-out and in-place mutation give from the caller's live bindings, with
last uses passed as places, and they agree with every binding live.
-/

namespace Stilt.Moving

open InPlace

variable {m : List Bool} {fr : Copy.Frame} {s : State}

theorem foldlM_congr {σ γ δ : Type} {f : σ → γ → Except Fault σ} {g : σ → δ → Except Fault σ}
    (h : γ → δ) : ∀ (l : List γ) (acc : σ), (∀ a ∈ l, ∀ acc, f acc a = g acc (h a)) →
      l.foldlM f acc = (l.map h).foldlM g acc
  | [], _, _ => rfl
  | a :: l, acc, hf => by
    simp only [List.foldlM_cons, List.map_cons, hf a List.mem_cons_self]
    cases g acc (h a) with
    | error => rfl
    | ok acc' => exact foldlM_congr h l acc' fun b hb => hf b (List.mem_cons_of_mem _ hb)

/-- Copy-in reads only live places, and a last use passes the value of its
variable. -/
theorem copy_enter_view (h : MAgrees m fr s) (captured : Copy.Frame) {bound : List (Name × Passed)}
    (hp : ∀ y x p, (y, Passed.place x p) ∈ bound → LiveAt x m (names fr))
    (hm : ∀ y x v, (y, Passed.moved x v) ∈ bound → LiveAt x m (names fr) ∧ fr.lookup x = some v) :
    Copy.frames.enter fr captured bound =
      Copy.frames.enter (keep m fr) captured (bound.map Moving.handOver) := by
  rw [copy_enter_eq, copy_enter_eq]
  refine foldlM_congr _ bound captured fun ya hya acc => ?_
  obtain ⟨y, q⟩ := ya
  cases q with
  | value v => rfl
  | place x p =>
    simp only [Moving.handOver, copyEnterStep, Copy.read, h.lookup_frame (hp y x p hya)]
  | moved x v =>
    obtain ⟨hl, hv⟩ := hm y x v hya
    show pure ((y, v) :: acc) = (fun w => (y, w) :: acc) <$> Copy.read (keep m fr) x []
    rw [show Copy.read (keep m fr) x [] = .ok v by simp [Copy.read, h.lookup_frame hl, hv, Value.get]]
    rfl

/-- In place, a call reads only live places. -/
theorem inPlace_enter_view (h : MAgrees m fr s) (captured : List (Name × Value))
    {bound : List (Name × Passed)} (hp : ∀ y x p, (y, Passed.place x p) ∈ bound → LiveAt x m (names fr)) :
    InPlace.frames.enter s captured bound =
      InPlace.frames.enter ⟨keep m s.env, s.store⟩ captured bound := by
  rw [enter_eq, enter_eq]
  have := foldlM_congr (f := enterStep s) (g := enterStep ⟨keep m s.env, s.store⟩) id bound
    (List.foldr (fun xv t => InPlace.bind t xv.1 xv.2) ⟨[], s.store⟩ captured) fun ya hya acc => ?_
  · rw [List.map_id] at this
    exact this
  obtain ⟨y, q⟩ := ya
  cases q with
  | value v | moved x v => rfl
  | place x p =>
    simp only [enterStep, id, h.lookup_env (hp y x p hya)]
    rfl

/-- The callee's frame holds values a run may hold. -/
theorem enter_just {caller captured frc : Copy.Frame} {bound : List (Name × Passed)}
    (hcap : ∀ xv ∈ captured, xv.2.Justified) (hcal : ∀ xv ∈ caller, xv.2.Justified)
    (hb : ∀ q ∈ bound.map Prod.snd, ∀ v, q.value? = some v → v.Justified)
    (h : Copy.frames.enter caller captured bound = .ok frc) : ∀ xv ∈ frc, xv.2.Justified := by
  rw [copy_enter_eq] at h
  induction bound generalizing captured with
  | nil => cases h; exact hcap
  | cons ya bound ih =>
    obtain ⟨y, q⟩ := ya
    simp only [List.foldlM_cons] at h
    cases hs : copyEnterStep caller captured (y, q) with
    | error e => rw [hs] at h; cases h
    | ok acc =>
      rw [hs] at h
      refine ih ?_ (fun q' hq' => hb q' (List.mem_cons_of_mem _ hq')) h
      intro xv hxv
      cases q with
      | value v | moved x v =>
        cases hs
        rcases List.mem_cons.1 hxv with rfl | hxv
        · exact hb _ List.mem_cons_self v rfl
        · exact hcap xv hxv
      | place x p =>
        simp only [copyEnterStep] at hs
        cases hr : Copy.read caller x p with
        | error e => rw [hr] at hs; cases hs
        | ok v =>
          rw [hr] at hs
          cases hs
          rcases List.mem_cons.1 hxv with rfl | hxv
          · unfold Copy.read at hr
            split at hr
            · rename_i w hw
              exact Value.Justified.get (hcal _ (mem_of_lookup hw)) hr
            · cases hr
          · exact hcap xv hxv

theorem Holds.names {st : List Value} :
    ∀ {fr : Copy.Frame} {env : List (Name × Ref)}, Holds st fr env → fr.map Prod.fst = env.map Prod.fst
  | [], [], _ => rfl
  | (_, _) :: _, (_, _) :: _, ⟨rfl, _, h⟩ => by simp [Holds.names h]
  | [], _ :: _, h | _ :: _, [], h => h.elim

theorem LiveAt.of_all {x : Name} : ∀ {m : List Bool} {ns : List Name}, (∀ b ∈ m, b = true) →
    LiveAt x m ns
  | [], _, _ | _ :: _, [], _ => trivial
  | b :: m, y :: ns, h => by
    unfold LiveAt
    split
    · exact h b List.mem_cons_self
    · exact LiveAt.of_all fun c hc => h c (List.mem_cons_of_mem _ hc)

theorem Inv.of_all {L : Live} {m : List Bool} {ns : List Name} (h : ∀ b ∈ m, b = true) : Inv L m ns :=
  ⟨fun _ _ => LiveAt.of_all h⟩

/-- The callee starts with every binding live. -/
theorem MAgrees.callee {frc : Copy.Frame} {sc : State} (h : Agrees frc sc)
    (hj : ∀ xv ∈ frc, xv.2.Justified) : MAgrees (List.replicate frc.length true) frc sc := by
  have hall : ∀ b ∈ List.replicate frc.length true, b = true := fun b hb => List.eq_of_mem_replicate hb
  have hn := Holds.names h.holds
  have hlen : frc.length = sc.env.length := by
    rw [← List.length_map (f := Prod.fst), hn, List.length_map]
  refine ⟨by simp, hn, ?_, h.valid, ?_⟩
  · rw [keep_all hall (by simp), keep_all hall (by simp [hlen])]
    exact h
  · rw [keep_all hall (by simp)]
    exact hj

end Stilt.Moving
